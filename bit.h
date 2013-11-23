/* Copyright (C) 1995 Danny Dube, Universite de Montreal. */
/* All rights reserved. */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Personnalisation */
#define TRUE 1
#define FALSE 0

/* Configuration */
#define CHARSPERINT (sizeof (int))
#define LOGCPI 2
#define DEFAULTHEAPSIZE 65536

/* Variables globales C */
extern int *mem;
extern int  mem_len, nb_handles, nb_obj, handle1;
extern int  mem_next, mem_free, mem_stack;
extern int  gc_mark, gc_compact, gc_ratio, gc_time;
extern int  gc_trav, gc_vecting, gc_cut;
extern int  gc_old, gc_new, gc_len, gc_src, gc_dst, gc_state;
extern int  nb_symbols;
extern int  eval_pc;
extern int (*cprim0[])(void);
extern int (*cprim1[])(int);
extern int (*cprim2[])(int, int);
extern int (*cprim3[])(int, int, int);

/* Variables globales SCM */
#define NBTEMPS 6
#define cons_car              (globs[0])
#define cons_cdr              (globs[1])
#define string_copy_s1        (globs[0])
#define make_clos_env         (globs[0])
#define list_copy_tete        (globs[2])
#define list_copy_courant     (globs[3])
#define list_copy_l           (globs[4])
#define make_rest_frame_frame (globs[5])

#define NBSINGLES 10
#define scm_empty            (globs[NBTEMPS + 0])
#define scm_false            (globs[NBTEMPS + 1])
#define scm_true             (globs[NBTEMPS + 2])
#define scm_symbol_names     (globs[NBTEMPS + 3])
#define scm_constants        (globs[NBTEMPS + 4])

#define eval_val             (globs[NBTEMPS + 5])
#define eval_env             (globs[NBTEMPS + 6])
#define eval_args            (globs[NBTEMPS + 7])
#define eval_prev_args       (globs[NBTEMPS + 8])
#define eval_cont            (globs[NBTEMPS + 9])

#define NBGLOBS (NBTEMPS + NBSINGLES)
extern int globs[];

/* Description des types et macros du GC */
#define BITH1 0x80000000
#define BITH2 0x40000000
#define BITB4 0x8
#define BITB3 0x4
#define BITB2 0x2
#define BITB1 0x1

#define NUMMASK     BITB1
#define NUMVAL      BITB1
#define TYPEMASK    (BITH1 | BITH2 | BITB1)
#define TYPEPAIR    0
#define TYPECLOS    BITH2
#define TYPEOTHER   BITH1
#define TYPESPEC    (BITH1 | BITH2)
#define CONTMASK    BITB1
#define CONTVAL     BITB1
#define VECTINGMASK (BITB2 | BITB1)
#define VECTORVAL   0
#define STRINGVAL   BITB2
#define SYMBMASK    (BITH1 | BITH2 | BITB2 | BITB1)
#define SYMBVAL     (BITH1 | BITH2 | BITB2)
#define SPECMASK    (BITH1 | BITH2 | BITB4 | BITB3 | BITB2 | BITB1)
#define SPECCHAR    (BITH1 | BITH2)
#define SPECCPRIM   (BITH1 | BITH2 | BITB3)
#define SPECBOOL    (BITH1 | BITH2 | BITB4)
#define NULLVAL     0xfffffffc
#define FALSEVAL    0xffffffe8
#define TRUEVAL     0xfffffff8
#define HANDLEMASK  (~TYPEMASK)

#define C_PRED_NUMBER(d)  (((d) & NUMMASK) == NUMVAL)
#define C_PRED_PAIR(d)    (((d) & TYPEMASK) == TYPEPAIR)
#define C_PRED_CLOSURE(d) (((d) & TYPEMASK) == TYPECLOS)
#define C_PRED_OTHER(d)   (((d) & TYPEMASK) == TYPEOTHER)
#define C_PRED_SPECIAL(d) (((d) & TYPEMASK) == TYPESPEC)
#define C_PRED_SYMBOL(d)  (((d) & SYMBMASK) == SYMBVAL)
#define C_PRED_CHAR(d)    (((d) & SPECMASK) == SPECCHAR)
#define C_PRED_CPRIM(d)   (((d) & SPECMASK) == SPECCPRIM)
#define C_PRED_BOOLEAN(d) (((d) & SPECMASK) == SPECBOOL)

#define GC_MARK         1
#define IS_MARKED(data) (mem[mem[SCM_TO_HANDLE(data)]] & GC_MARK)

/* Fonctions de manipulation des donnees */

#define SCM_TO_HANDLE(d)     (((d) & HANDLEMASK) >> 1)
#define HANDLE_TO_PAIR(i)    (((i) << 1) | TYPEPAIR)
#define HANDLE_TO_CLOSURE(i) (((i) << 1) | TYPECLOS)
#define HANDLE_TO_OTHER(i)   (((i) << 1) | TYPEOTHER)
#define TO_SCM_CHAR(c)       (((c) << 4) | SPECCHAR)
#define TO_C_CHAR(c)         (((c) >> 4) & 0xff)
#define C_STRING_LEN(s)      (mem[mem[SCM_TO_HANDLE(s)] + 1] >> 2)
#define SYMBOL_NUMBER(s)     (((s) & ~SYMBMASK) >> 2)
#define NUMBER_TO_SYMBOL(n)  (((n) << 2) | SYMBVAL)
#define TO_SCM_NUMBER(n)     (((n) << 1) | NUMVAL)
#define C_VECTOR_LEN(v)      (mem[mem[SCM_TO_HANDLE(v)] + 1] >> 2)
#define C_MAKE_CPRIM(n)      (((n) << 4) | SPECCPRIM)
#define CPRIM_NUMBER(c)      (((c) & ~SPECMASK) >> 4)
#define PC_TO_PCTAG(p)       (((p) << 1) | CONTVAL)
#define PCTAG_TO_PC(p)       ((p) >> 1)
#define CHAMP(d,champ)       (mem[mem[SCM_TO_HANDLE(d)] + 1 + (champ)])

/* Description des primitives C */
#define NBCPRIM0 4
#define FIRSTCPRIM0 0
#define NBCPRIM1 21
#define FIRSTCPRIM1 (FIRSTCPRIM0 + NBCPRIM0)
#define NBCPRIM2 14
#define FIRSTCPRIM2 (FIRSTCPRIM1 + NBCPRIM1)
#define NBCPRIM3 2
#define FIRSTCPRIM3 (FIRSTCPRIM2 + NBCPRIM2)
#define APPLY_CPRIM_NO 36

/* Variables du module Scheme compile */
extern int bytecode_len;
extern unsigned char bytecode[];
extern int const_desc_len;
extern unsigned char const_desc[];
extern int nb_scm_globs;
extern int scm_globs[];

/* Prototypes de bit.c */
void  alloc_heap(int taille);
int   is_allocated(int d);
void  mark_it(int d);
void  gc(int size);
int   alloc_cell(int len, int bitpattern);
int   pred_boolean(int d);
int   pred_pair(int d);
int   cons(int car, int cdr);
int   car(int p);
int   cdr(int p);
int   set_car(int p, int d);
int   set_cdr(int p, int d);
int   list_copy(int l);
int   pred_char(int d);
int   integer_to_char(int n);
int   char_to_integer(int c);
int   c_pred_string(int d);
int   pred_string(int d);
int   c_make_string(int len);
int   make_string(int len);
char *find_string_base(int s, int pos);
int   c_string_ref(int s, int pos);
int   string_ref(int s, int pos);
void  c_string_set(int s, int pos, int c);
int   string_set(int s, int pos, int c);
int   string_length(int s);
int   string_len_to_int_string_len(int len);
int   c_string_int_len(int s);
int   to_scm_string(char *cs, int len);
int   c_string_equal(int s1, int s2);
int   string_equal(int s1, int s2);
int   string_copy(int s1);
int   pred_symbol(int d);
void  stretch_symbol_vector(void);
int   make_symbol(int nom);
int   symbol_to_string(int s);
int   string_to_symbol(int string);
int   pred_number(int d);
int   to_c_number(int n);
int   cppoe2(int n1, int n2);
int   cplus2(int n1, int n2);
int   cmoins2(int n1, int n2);
int   cfois2(int n1, int n2);
int   cdivise2(int n1, int n2);
int   c_pred_vector(int d);
int   pred_vector(int d);
int   c_make_vector(int len);
int   make_vector(int len);
int   find_vector_location(int v, int pos);
int   c_vector_ref(int v, int pos);
int   vector_ref(int v, int pos);
void  c_vector_set(int v, int pos, int val);
int   vector_set(int v, int pos, int val);
int   vector_length(int v);
int   vector_len_to_int_vector_len(int len);
int   c_vector_int_len(int v);
int   pred_procedure(int d);
int   make_closure(int entry, int env);
int   closure_entry(int c);
int   closure_env(int c);
int   apply(int c, int args);
int   c_pred_cont(int d);
int   make_cont(void);
void  set_cont_pc(int k, int dest);
void  restore_cont(int k);
int   ll_input(void);
int   c_peek_char(void);
int   peek_char(void);
int   c_read_char(void);
int   read_char(void);
int   write_char(int c);
int   eq(int d1, int d2);
int   quit(void);
int   return_current_continuation(void);
int   return_there_with_this(int complete_cont, int val);
int   introspection(int arg);
void  init_bc_reader(void);
int   read_bc_byte(void);
int   read_bc_int(void);
int   get_frame(int step);
int   get_var(int frame, int offset);
void  set_var(int frame, int offset, int val);
void  make_normal_frame(int size);
void  make_rest_frame(int size);
void  push_arg(int arg);
int   pop_arg(void);
void  pop_n_args(int n);
int   apply_cprim(int cprim_no, int args);
int   apply_closure(int c, int args);
void  c_apply(int c, int args);
void  execute_bc(void);
int   init_scm_glob_1(int code);
int   init_scm_glob_2(int code);
int   main(int argc, char *argv[]);
