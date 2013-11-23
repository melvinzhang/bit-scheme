/* Copyright (C) 1995 Danny Dube, Universite de Montreal. */
/* All rights reserved. */

/* Mini interprete Scheme. Troisieme d'une serie. */
/* Ne traite pas: */
/*     les ports, */
/*     les points flottants, */
/*     les entiers de taille illimitee, */
/*     l'entree de nombres non-decimaux. */

#include "bit.h"




/* Variables globales C ----------------------------------------- */

int *mem;
int  mem_len, nb_handles, nb_obj, handle1, mem_next, mem_free, mem_stack;
int  gc_mark, gc_compact, gc_ratio, gc_time, gc_trav, gc_vecting, gc_cut;
int  gc_old, gc_new, gc_len, gc_src, gc_dst, gc_state;

int nb_symbols;

int eval_pc;

int (*cprim0[NBCPRIM0])(void) =
{
  peek_char,
  read_char,
  quit,
  return_current_continuation
};

int (*cprim1[NBCPRIM1])(int) =
{
  pred_boolean,
  pred_pair,
  car,
  cdr,
  pred_char,
  integer_to_char,
  char_to_integer,
  pred_string,
  make_string,
  string_length,
  string_copy,
  pred_symbol,
  symbol_to_string,
  string_to_symbol,
  pred_number,
  pred_vector,
  make_vector,
  vector_length,
  pred_procedure,
  write_char,
  introspection
};

int (*cprim2[NBCPRIM2])(int, int) =
{
  cons,
  set_car,
  set_cdr,
  string_ref,
  string_equal,
  cppoe2,
  cplus2,
  cmoins2,
  cfois2,
  cdivise2,
  vector_ref,
  apply,
  eq,
  return_there_with_this
};

int (*cprim3[NBCPRIM3])(int, int, int) =
{
  string_set,
  vector_set
};




/* Variables globales SCM --------------------------------------- */

/* Les variables contenues dans stack */
/* doivent etre mises a jour par le gc */
int globs[NBGLOBS];




/* Allocation du monceau ---------------------------------------- */

void alloc_heap(int taille)
{
  int j;

  mem_len = taille;
  mem = malloc(mem_len * (sizeof (int)));
  if (mem == NULL)
    {
      fprintf(stderr, "Incapable d'allouer le monceau\n");
      exit(1);
    }
  nb_handles = (mem_len + 4) / 5;
  nb_obj = 0;
  handle1 = 0;
  for (j=0 ; j<nb_handles ; j++)
    mem[j] = j + 1;
  mem[nb_handles - 1] = -1;
  mem_next = nb_handles;
  mem_free = mem_len - mem_next;
  gc_mark = FALSE;
  gc_compact = FALSE;
  gc_ratio = 2;
  gc_time = 0;
  gc_vecting = FALSEVAL;
  gc_state = 0;
}




/* Garbage collector -------------------------------------------- */

int is_allocated(int d)
{
  return !C_PRED_NUMBER(d) && !C_PRED_SPECIAL(d);
}

void mark_it(int d)
{
  if (!is_allocated(d))
    return;
  if (IS_MARKED(d))
    return;
  mem[mem[SCM_TO_HANDLE(d)]] |= GC_MARK;
  mem_stack --;
  mem[mem_stack] = d;
}

/* La description des etats est ailleurs */
/* Note: mem_free n'est maintenu qu'entre deux phases de GC */
/* Note: meme chose pour nb_obj */
void gc(int size)
{
  int court, start, j, nbcases, marque, d, handle, subnlen;

  gc_time += size + size;    /* Simuler une multiplication rapide */
  if (gc_ratio >= 3)
    {
      gc_time += size;
      if (gc_ratio >= 4)
	{
	  gc_time += size;
	  if (gc_ratio >=5)
	    gc_time += size * (gc_ratio - 4);
	}
    }

  while (gc_time > 0)
    switch (gc_state)
      {
      case 0:
	{
	  if (mem_free == 0)
	    gc_ratio = mem_len;
	  else
	    gc_ratio = (2 * (mem_next - nb_handles) + 
			2 * nb_obj +
			2 * nb_scm_globs +
			(5 * mem_free + 1) / 2 -
			1) / mem_free;
	  gc_time += size * gc_ratio;   /* Car le ratio etait insuffisant */
	  gc_time -= (gc_ratio *
		      (((2 * gc_ratio - 3) * mem_free -
			4 * (mem_next - nb_handles) -
			4 * nb_obj -
			4 * nb_scm_globs) /
		       (2 * gc_ratio + 1)));
	  gc_time += 50;                /* Securite! */
	  gc_state = 1;
	  break;
	}
      case 1:
	{
	  mem_stack = mem_len;
	  gc_mark = TRUE;
	  gc_cut = 0;
	  gc_state = 2;
	  break;
	}
      case 2:
	{
	  nbcases = ((nb_scm_globs - gc_cut <= gc_time) ?
		     nb_scm_globs - gc_cut :
		     gc_time);
	  for (j=gc_cut ; j<gc_cut+nbcases ; j++)
	    mark_it(scm_globs[j]);
	  gc_time -= nbcases;
	  gc_cut += nbcases;
	  gc_state = (gc_cut == nb_scm_globs) ? 5 : 2;
	  break;
	}
      case 3:
	{
	  if (mem_stack == mem_len)
	    gc_state = 5;
	  else
	    {
	      gc_trav = mem[mem_stack];
	      mem_stack ++;
	      gc_src = mem[SCM_TO_HANDLE(gc_trav)];
	      switch (gc_trav & TYPEMASK)
		{
		case TYPEPAIR:                       /* PAIR */
		  {
		    start = 1;
		    gc_len = 3;
		    break;
		  }
		case TYPECLOS:                       /* CLOSURE */
		  {
		    start = 2;
		    gc_len = 3;
		    break;
		  }
		default:
		  {
		    subnlen = mem[gc_src + 1];
		    if (subnlen & CONTMASK)          /* CONT */
		      {
			start = 2;
			gc_len = 5;
		      }
		    else if (subnlen & VECTINGMASK)  /* STRING */
		      {
			start =
			  2 + string_len_to_int_string_len(subnlen >> 2);
			gc_len = start;
		      }
		    else                             /* VECTOR */
		      {
			gc_len =
			  2 + vector_len_to_int_vector_len(subnlen >> 2);
			gc_cut = 2;
			gc_time -= 3;
			gc_state = 4;
			goto label001;
		      }
		  }
		}
	      for (j=start ; j<gc_len ; j++)
		mark_it(mem[gc_src + j]);
	      gc_time -= gc_len + 1;
	      gc_state = 3;
	    }
	label001:
	  break;
	}
      case 4:
	{
	  nbcases = (gc_len - gc_cut <= gc_time) ? gc_len - gc_cut : gc_time;
	  for (j=0 ; j<nbcases ; j++)
	    mark_it(mem[gc_src + gc_cut + j]);
	  gc_time -= nbcases;
	  gc_cut += nbcases;
	  gc_state = (gc_cut == gc_len) ? 3 : 4;
	  break;
	}
      case 5:
	{
	  for (j=0 ; j<NBGLOBS ; j++)
	    mark_it(globs[j]);
	  gc_state = (mem_stack == mem_len) ? 6 : 3;
	  break;
	}
      case 6:
	{
	  gc_mark = FALSE;
	  gc_compact = TRUE;
	  gc_src = nb_handles;
	  gc_dst = nb_handles;
	  gc_state = 7;
	  nb_obj = 0;
	  break;
	}
      case 7:
	{
	  gc_state = (gc_src == mem_next) ? 10 : 8;
	  break;
	}
      case 8:
	{
	  d = mem[gc_src];
	  marque = d & GC_MARK;
	  d &= ~GC_MARK;
	  mem[gc_src] = d;
	  switch(d & TYPEMASK)
	    {
	    case TYPEPAIR:                       /* PAIR */
	    case TYPECLOS:                       /* CLOSURE */
	      {
		court = TRUE;
		gc_len = 3;
		break;
	      }
	    default:
	      {
		subnlen = mem[gc_src + 1];
		if (subnlen & CONTMASK)          /* CONT */
		  {
		    court = TRUE;
		    gc_len = 5;
		    break;
		  }
		else if (subnlen & VECTINGMASK)  /* STRING */
		  {
		    court = FALSE;
		    gc_len =
		      2 + string_len_to_int_string_len(subnlen >> 2);
		    break;
		  }
		else                             /* VECTOR */
		  {
		    court = FALSE;
		    gc_len =
		      2 + vector_len_to_int_vector_len(subnlen >> 2);
		    break;
		  }
	      }
	    }
	  handle = SCM_TO_HANDLE(d);
	  if (!marque)
	    {
	      mem[handle] = handle1;
	      handle1 = handle;
	      gc_time -= gc_len + 1;
	      gc_src += gc_len;
	      gc_state = 7;
	    }
	  else if (court)
	    {
	      mem[handle] = gc_dst;
	      for (j=0 ; j<gc_len ; j++)
		mem[gc_dst + j] = mem[gc_src + j];
	      nb_obj ++;
	      gc_time -= gc_len + 1;
	      gc_src += gc_len;
	      gc_dst += gc_len;
	      gc_state = 7;
	    }
	  else
	    {
	      mem[handle] = gc_dst;
	      mem[gc_dst] = mem[gc_src];
	      mem[gc_dst + 1] = mem[gc_src + 1];
	      nb_obj ++;
	      gc_time -= 3;
	      gc_vecting = d;
	      gc_cut = 2;
	      gc_old = gc_src;
	      gc_new = gc_dst;
	      gc_dst += gc_len;
	      gc_state = 9;
	    }
	  break;
	}
      case 9:
	{
	  nbcases = (gc_len - gc_cut <= gc_time) ? gc_len - gc_cut : gc_time;
	  for (j=0 ; j<nbcases ; j++)
	    mem[gc_new + gc_cut + j] = mem[gc_old + gc_cut + j];
	  gc_time -= nbcases;
	  gc_cut += nbcases;
	  if (gc_cut == gc_len)
	    {
	      gc_vecting = scm_false;
	      gc_src += gc_len;
	      gc_state = 7;
	    }
	  else
	    gc_state = 9;
	  break;
	}
      case 10:
	{
	  mem_next = gc_dst;
/*	  printf("%s %d cases pour %d objets, ratio de %d, reste %d\n",
		 "GC completed:", mem_next - nb_handles,
		 nb_obj, gc_ratio, mem_free);  */
	  mem_free = mem_len - mem_next - nb_obj;
	  gc_compact = FALSE;
	  gc_ratio = 1;
	  gc_time = 0;
	  gc_state = 0;
	  if (mem_free < size)
	    {
	      fprintf(stderr, "Manque de memoire\n");
	      exit(1);
	    }
	  break;
	}
      }
}




/* Fonction d'allocation de memoire ----------------------------- */

/* Un appel a cette fonction peut declencher le gc */
int alloc_cell(int len, int bitpattern)
{
  int j, pos, handle, d, marque;

  gc(len + 1);

  if (gc_compact)
    {
      if (gc_dst + len <= gc_src)
	{
	  pos = gc_dst;
	  gc_dst += len;
	  marque = 0;
	}
      else
	{
	  pos = mem_next;
	  mem_next += len;
	  marque = GC_MARK;
	}
    }
  else
    {
      pos = mem_next;
      mem_next += len;
      marque = 0;
    }

  handle = handle1;
  handle1 = mem[handle1];
  mem[handle] = pos;

  d = (handle << 1) | bitpattern;

  mem[pos] = d | marque;
  
  return d;
}




/* Fonctions relatives a BOOLEAN -------------------------------- */

int pred_boolean(int d)
{
  return C_PRED_BOOLEAN(d) ? scm_true : scm_false;
}




/* Fonctions relatives a PAIR ----------------------------------- */

int pred_pair(int d)
{
  return C_PRED_PAIR(d) ? scm_true : scm_false;
}

int cons(int car, int cdr)
{
  int handle, cell, pair;

  cons_car = car;
  cons_cdr = cdr;
  pair = alloc_cell(3, TYPEPAIR);
  handle = SCM_TO_HANDLE(pair);
  cell = mem[handle];
  mem[cell + 1] = cons_car;
  mem[cell + 2] = cons_cdr;
  return pair;
}

int car(int p)
{
  return CHAMP(p, 0);
}

int cdr(int p)
{
  return CHAMP(p, 1);
}

int set_car(int p, int d)
{
  if (gc_mark && IS_MARKED(p))
    mark_it(d);
  CHAMP(p, 0) = d;
  return scm_true;
}

int set_cdr(int p, int d)
{
  if (gc_mark && IS_MARKED(p))
    mark_it(d);
  CHAMP(p, 1) = d;
  return scm_true;
}

int list_copy(int l)
{
  int temp;

  if (l == scm_empty)
    return l;
  else
    {
      list_copy_l = l;
      list_copy_courant = list_copy_tete = cons(car(list_copy_l), scm_empty);
      list_copy_l = cdr(list_copy_l);
      while (list_copy_l != scm_empty)
	{
	  temp = cons(car(list_copy_l), scm_empty);
	  set_cdr(list_copy_courant, temp);
	  list_copy_l = cdr(list_copy_l);
	  list_copy_courant = cdr(list_copy_courant);
	}
      return list_copy_tete;
    }
}




/* Fonctions relatives a CHAR ----------------------------------- */

int pred_char(int d)
{
  return C_PRED_CHAR(d) ? scm_true : scm_false;
}

int integer_to_char(int n)
{
  return TO_SCM_CHAR(to_c_number(n));
}

int char_to_integer(int c)
{
  return TO_SCM_NUMBER(TO_C_CHAR(c));
}




/* Fonctions relatives a STRING --------------------------------- */

int c_pred_string(int d)
{
  return (C_PRED_OTHER(d) &&
	  ((mem[mem[SCM_TO_HANDLE(d)] + 1] & VECTINGMASK) == STRINGVAL));
}

int pred_string(int d)
{
  return c_pred_string(d) ? scm_true : scm_false;
}

int c_make_string(int len)
{
  int intlen, handle, cell, string;

  intlen = string_len_to_int_string_len(len);
  string = alloc_cell(2 + intlen, TYPEOTHER);
  handle = SCM_TO_HANDLE(string);
  cell = mem[handle];
  mem[cell + 1] = (len << 2) | STRINGVAL;
  return string;
}

int make_string(int len)
{
  return c_make_string(to_c_number(len));
}

char *find_string_base(int s, int pos)
{
  int intpos;

  if (s != gc_vecting)
    return (char *) (&mem[mem[SCM_TO_HANDLE(s)] + 2]);
  else
    {
      intpos = (pos >> LOGCPI) + 2;
      if (intpos >= gc_cut)
	return (char *) (&mem[gc_old + 2]);
      else
	return (char *) (&mem[gc_new + 2]);
    }
}

int c_string_ref(int s, int pos)
{
  char *base;

  base = find_string_base(s, pos);
  return (int) (*(base + pos));
}

int string_ref(int s, int pos)
{
  return TO_SCM_CHAR(c_string_ref(s, to_c_number(pos)));
}

void c_string_set(int s, int pos, int c)
{
  char *base;

  base = find_string_base(s, pos);
  *(base + pos) = (char) c;
}

int string_set(int s, int pos, int c)
{
  c_string_set(s, to_c_number(pos), TO_C_CHAR(c));
  return scm_true;
}

int string_length(int s)
{
  return TO_SCM_NUMBER(C_STRING_LEN(s));
}

int string_len_to_int_string_len(int len)
{
  int intlen;

  intlen = (len + CHARSPERINT - 1) >> LOGCPI;
  return (intlen == 0) ? 1 : intlen;
}

int c_string_int_len(int s)
{
  return string_len_to_int_string_len(C_STRING_LEN(s));
}

int to_scm_string(char *cs, int len)
{
  int i, scms;

  scms = c_make_string(len);
  for (i=0 ; i<len ; i++)
    c_string_set(scms, i, cs[i]);
  return scms;
}

int c_string_equal(int s1, int s2)
{
  int   len1, len2, i;

  len1 = C_STRING_LEN(s1);
  len2 = C_STRING_LEN(s2);

  if (len1 != len2)
    return FALSE;

  for (i=0 ; i<len1 ; i++)
    if (c_string_ref(s1, i) != c_string_ref(s2, i))
      return FALSE;
  return TRUE;
}

int string_equal(int s1, int s2)
{
  return c_string_equal(s1, s2) ? scm_true : scm_false;
}

int string_copy(int s1)
{
  int   len, i;
  int   s2;

  len = C_STRING_LEN(s1);
  string_copy_s1 = s1;
  s2 = c_make_string(len);
  for (i=0 ; i<len ; i++)
    c_string_set(s2, i, c_string_ref(string_copy_s1, i));
  return s2;
}




/* Fonctions relatives a SYMBOL --------------------------------- */

int pred_symbol(int d)
{
  return C_PRED_SYMBOL(d) ? scm_true : scm_false;
}

void stretch_symbol_vector(void)
{
  int oldlen, newlen, j;
  int newnames;

  oldlen = C_VECTOR_LEN(scm_symbol_names);
  newlen = (4 * oldlen) / 3 + 1;
  newnames = c_make_vector(newlen);
  for (j=0 ; j<nb_symbols ; j++)
    c_vector_set(newnames, j, c_vector_ref(scm_symbol_names, j));
  scm_symbol_names = newnames;
}

/* Cette fonction ne doit etre utilisee */
/* que par string->symbol */
int make_symbol(int nom)
{
  int numero;

  if (nb_symbols == C_VECTOR_LEN(scm_symbol_names))
    stretch_symbol_vector();

  numero = nb_symbols;
  nb_symbols ++;
  c_vector_set(scm_symbol_names, numero, nom);

  return NUMBER_TO_SYMBOL(numero);
}

int symbol_to_string(int s)
{
  return c_vector_ref(scm_symbol_names, SYMBOL_NUMBER(s));
}

int string_to_symbol(int string)
{
  int j;

  for (j=0 ; j<nb_symbols ; j++)
    if (c_string_equal(string, c_vector_ref(scm_symbol_names, j)))
      return NUMBER_TO_SYMBOL(j);

  return make_symbol(string_copy(string));
}




/* Fonctions relatives a NUMBER --------------------------------- */

int pred_number(int d)
{
  return C_PRED_NUMBER(d) ? scm_true : scm_false;
}

int to_c_number(int n)
{
  if (n < 0)
    return (n >> 1) | BITH1;
  else
    return n >> 1;
}

/* Les op. se font AVEC les tags */
int cppoe2(int n1, int n2)
{
  return (n1 <= n2) ? scm_true : scm_false;
}

int cplus2(int n1, int n2)
{
  return n1 + n2 - NUMVAL;
}

int cmoins2(int n1, int n2)
{
  return n1 - n2 + NUMVAL;
}

int cfois2(int n1, int n2)
{
  return TO_SCM_NUMBER(to_c_number(n1) * to_c_number(n2));
}

int cdivise2(int n1, int n2)
{
  return TO_SCM_NUMBER(to_c_number(n1) / to_c_number(n2));
}




/* Fonctions relatives a VECTOR --------------------------------- */

int c_pred_vector(int d)
{
  return (C_PRED_OTHER(d) &&
	  ((mem[mem[SCM_TO_HANDLE(d)] + 1] & VECTINGMASK) == VECTORVAL));
}

int pred_vector(int d)
{
  return c_pred_vector(d) ? scm_true : scm_false;
}

int c_make_vector(int len)
{
  int intlen, j;
  int cell, handle, vector;

  intlen = vector_len_to_int_vector_len(len);
  vector = alloc_cell(2 + intlen, TYPEOTHER);
  handle = SCM_TO_HANDLE(vector);
  cell = mem[handle];
  mem[cell + 1] = (len << 2) | VECTORVAL;
  for (j=0 ; j<intlen ; j++)
    mem[cell + j + 2] = scm_false;
  return vector;
}

int make_vector(int len)
{
  return c_make_vector(to_c_number(len));
}

int find_vector_location(int v, int pos)
{
  if (v != gc_vecting)
    return mem[SCM_TO_HANDLE(v)];
  else if (2 + pos >= gc_cut)
    return gc_old;
  else
    return gc_new;
}

int c_vector_ref(int v, int pos)
{
  int location;

  location = find_vector_location(v, pos);
  return mem[location + 2 + pos];
}

int vector_ref(int v, int pos)
{
  return c_vector_ref(v, to_c_number(pos));
}

void c_vector_set(int v, int pos, int val)
{
  int location;

  if (gc_mark && IS_MARKED(v))
    mark_it(val);
  location = find_vector_location(v, pos);
  mem[location + 2 + pos] = val;
}

int vector_set(int v, int pos, int val)
{
  c_vector_set(v, to_c_number(pos), val);
  return scm_true;
}

int vector_length(int v)
{
  return TO_SCM_NUMBER(C_VECTOR_LEN(v));
}

int vector_len_to_int_vector_len(int len)
{
  return (len == 0) ? 1 : len;
}

int c_vector_int_len(int v)
{
  return vector_len_to_int_vector_len(C_VECTOR_LEN(v));
}




/* Fonctions relatives a PROCEDURE ------------------------------ */

int pred_procedure(int d)
{
  return (C_PRED_CPRIM(d) || C_PRED_CLOSURE(d)) ? scm_true : scm_false;
}

int make_closure(int entry, int env)
{
  int cell, handle, closure;

  make_clos_env = env;
  closure = alloc_cell(3, TYPECLOS);
  handle = SCM_TO_HANDLE(closure);
  cell = mem[handle];
  mem[cell + 1] = entry;
  mem[cell + 2] = make_clos_env;
  return closure;
}

int closure_entry(int c)
{
  return CHAMP(c, 0);
}

int closure_env(int c)
{
  return CHAMP(c, 1);
}

/* Cette fonction ne peut appeler direct. c_apply */
/* Note: elle utilise le apply-hook a la fin du bytecode */
int apply(int c, int args)
{
  eval_pc = bytecode_len - 1;
  eval_args = cons(c, args);
  return scm_false;
}




/* Fonctions relatives a CONT ----------------------------------- */

int c_pred_cont(int d)
{
  return (C_PRED_OTHER(d) &&
	  ((mem[mem[SCM_TO_HANDLE(d)] + 1] & CONTMASK) == CONTVAL));
}

int make_cont(void)
{
  int cell, handle, k;

  k = alloc_cell(5, TYPEOTHER);
  handle = SCM_TO_HANDLE(k);
  cell = mem[handle];
  mem[cell + 1] = PC_TO_PCTAG(eval_pc);
  mem[cell + 2] = eval_env;
  mem[cell + 3] = eval_args;
  mem[cell + 4] = eval_cont;
  return k;
}

void set_cont_pc(int k, int dest)
{
  CHAMP(k, 0) = PC_TO_PCTAG(dest);
}

void restore_cont(int k)
{
  int cell;

  cell = mem[SCM_TO_HANDLE(k)];
  eval_pc = PCTAG_TO_PC(mem[cell + 1]);
  eval_env = mem[cell + 2];
  eval_args = mem[cell + 3];
  eval_cont = mem[cell + 4];
}




/* Fonctions d'entree/sortie ------------------------------------ */

int ll_input(void)
{
  int c;

  c = getchar();
  if (c == EOF)
    {
      printf("EOF\nQuit\n");
      exit(0);
    }
  return c;
}

static int look_ahead;
static int look_ahead_valide;

int c_peek_char(void)
{
  if (!look_ahead_valide)
    {
      look_ahead = ll_input();
      look_ahead_valide = TRUE;
    }
  return look_ahead;
}

int peek_char(void)
{
  return TO_SCM_CHAR(c_peek_char());
}

int c_read_char(void)
{
  if (look_ahead_valide)
    {
      look_ahead_valide = FALSE;
      return look_ahead;
    }
  else
    return ll_input();
}

int read_char(void)
{
  return TO_SCM_CHAR(c_read_char());
}

int write_char(int c)
{
  printf("%c", TO_C_CHAR(c));
  return scm_true;
}




/* Autres fonctions de la librairie ----------------------------- */

int eq(int d1, int d2)
{
  return (d1 == d2) ? scm_true : scm_false;
}

int quit(void)
{
  printf("Quit\n");
  exit(0);
}

int return_current_continuation(void)
{
  int temp;

  temp = make_cont();
  return cons(temp, eval_prev_args);
}

int return_there_with_this(int complete_cont, int val)
{
  eval_prev_args = cdr(complete_cont);
  restore_cont(car(complete_cont));
  return val;
}




/* Fonctions relatives au coeur de l'interprete ----------------- */

static int intro_state;

int introspection(int arg)
{
  if (intro_state == 0)
    {
      intro_state = 1;
      return scm_constants;
    }
  else
    {
      scm_constants = arg;
      return scm_false;
    }
}




/* Le coeur de l'interprete ------------------------------------- */

void init_bc_reader(void)
{
  eval_pc = 0;
  return;
}

int read_bc_byte(void)
{
  int b;

  b = (int) bytecode[eval_pc];
  eval_pc ++;
  return b;
}

int read_bc_int(void)
{
  int msb;

  msb = read_bc_byte();
  return (256 * msb + read_bc_byte());
}

int get_frame(int step)
{
  int frame;

  frame = eval_env;
  while (step > 0)
    {
      if (C_PRED_PAIR(frame))
	frame = car(frame);
      else
	frame = c_vector_ref(frame, 0);
      step --;
    }
  return frame;
}

int get_var(int frame, int offset)
{
  int f;

  f = get_frame(frame);
  if (C_PRED_PAIR(f))
    return cdr(f);
  else
    return c_vector_ref(f, 1 + offset);
}

void set_var(int frame, int offset, int val)
{
  int f;

  f = get_frame(frame);
  if (C_PRED_PAIR(f))
    set_cdr(f, val);
  else
    c_vector_set(f, 1 + offset, val);
}

void make_normal_frame(int size)
{
  int pos;
  int larg, frame;

  if (size == 1)
    eval_env = cons(eval_env, car(eval_args));
  else
    {
      frame = c_make_vector(size + 1);
      c_vector_set(frame, 0, eval_env);
      larg = eval_args;
      for (pos=1 ; pos<=size ; pos++)
	{
	  c_vector_set(frame, pos, car(larg));
	  larg = cdr(larg);
	}
      eval_env = frame;
    }
}

void make_rest_frame(int size)
{
  int pos;
  int larg;
  int temp;

  if (size == 1)
    {
      temp = list_copy(eval_args);
      eval_env = cons(eval_env, temp);
    }
  else
    {
      make_rest_frame_frame = c_make_vector(1 + size);
      c_vector_set(make_rest_frame_frame, 0, eval_env);
      larg = eval_args;
      for (pos=1 ; pos<size ; pos++)
	{
	  c_vector_set(make_rest_frame_frame, pos, car(larg));
	  larg = cdr(larg);
	}
      temp = list_copy(larg);
      c_vector_set(make_rest_frame_frame, size, temp);
      eval_env = make_rest_frame_frame;
    }
}

void push_arg(int arg)
{
  eval_args = cons(arg, eval_args);
}

int pop_arg(void)
{
  int temp;

  temp = car(eval_args);
  eval_args = cdr(eval_args);
  return temp;
}

void pop_n_args(int n)
{
  int i;

  for (i=0 ; i<n ; i++)
    pop_arg();
}

int apply_cprim(int cprim_no, int args)
{
  int arg1, arg2, arg3;

  if (cprim_no < FIRSTCPRIM1)
    return (*cprim0[cprim_no])();
  arg1 = car(args);
  if (cprim_no < FIRSTCPRIM2)
    return (*cprim1[cprim_no - FIRSTCPRIM1])(arg1);
  args = cdr(args);
  arg2 = car(args);
  if (cprim_no < FIRSTCPRIM3)
    return (*cprim2[cprim_no - FIRSTCPRIM2])(arg1, arg2);
  args = cdr(args);
  arg3 = car(args);
  return (*cprim3[cprim_no - FIRSTCPRIM3])(arg1, arg2, arg3);
}

int apply_closure(int c, int args)
{
  eval_pc = closure_entry(c);
  eval_args = args;
  eval_env = closure_env(c);
  return scm_false;
}

void c_apply(int c, int args)
{
  int cprim_no;
  int temp;

  if (C_PRED_CPRIM(c))  /* Dans une application generale, */
    {                   /* il faut forcer la restoration */
      cprim_no = CPRIM_NUMBER(c);
      temp = apply_cprim(cprim_no, args);
      if (cprim_no != APPLY_CPRIM_NO)
	{
	  restore_cont(eval_cont);
	  push_arg(temp);
	}
    }
  else
    apply_closure(c, args);
}

void execute_bc(void)
{
  int op, dest, frameno, offsetno;
  int frame;
  int (*read_bc_info)(void);

  init_bc_reader();
  while (TRUE)
    {
      op = read_bc_byte();
      switch (op)
	{
	case 0:
	  {
	    read_bc_info = read_bc_byte;
	    goto label002;
	  }
	case 1:
	  {
	    read_bc_info = read_bc_int;
	  label002:
	    push_arg(c_vector_ref(scm_constants, read_bc_info()));
	    break;
	  }
	case 2:
	  {
	    read_bc_info = read_bc_byte;
	    goto label003;
	  }
	case 3:
	  {
	    read_bc_info = read_bc_int;
	  label003:
	    frame = get_frame(read_bc_info());
	    if (C_PRED_PAIR(frame))
	      eval_val = cdr(frame);
	    else
	      eval_val = c_vector_ref(frame, 1 + read_bc_info());
	    push_arg(eval_val);
	    break;
	  }
	case 4:
	  {
	    read_bc_info = read_bc_byte;
	    goto label004;
	  }
	case 5:
	  {
	    read_bc_info = read_bc_int;
	  label004:
	    push_arg(scm_globs[read_bc_info()]);
	    break;
	  }
	case 6:
	  {
	    read_bc_info = read_bc_byte;
	    goto label005;
	  }
	case 7:
	  {
	    read_bc_info = read_bc_int;
	  label005:
	    frame = get_frame(read_bc_info());
	    eval_val = pop_arg();
	    if (C_PRED_PAIR(frame))
	      set_cdr(frame, eval_val);
	    else
	      c_vector_set(frame, 1 + read_bc_info(), eval_val);
	    push_arg(scm_false);
	    break;
	  }
	case 8:
	  {
	    read_bc_info = read_bc_byte;
	    goto label006;
	  }
	case 9:
	  {
	    read_bc_info = read_bc_int;
	  label006:
	    eval_val = pop_arg();
	    if (gc_mark)
	      mark_it(eval_val);
	    scm_globs[read_bc_info()] = eval_val;
	    push_arg(scm_false);
	    break;
	  }
	case 10:
	  {
	    eval_val = make_closure(eval_pc, eval_env);
	    restore_cont(eval_cont);
	    push_arg(eval_val);
	    break;
	  }
	case 11:
	  {
	    dest = read_bc_int();
	    if (pop_arg() == scm_false)
	      eval_pc = dest;
	    break;
	  }
	case 19:
	  {
	    set_cont_pc(eval_cont, eval_pc + 2);
	    /* continue to 13 */
	  }
	case 13:
	  {
	    eval_env = scm_empty;
	    /* continue to 12 */
	  }
	case 12:
	  {
	    eval_pc = read_bc_int();
	    break;
	  }
	case 14:
	  {
	    eval_val = eval_args;
	    restore_cont(eval_cont);
	    set_cdr(eval_val, eval_args);
	    eval_args = eval_val;
	    break;
	  }
	case 25:
	  {
	    eval_prev_args = cons(eval_args, eval_prev_args);
	    /* continue to 15 */
	  }
	case 15:
	  {
	    eval_args = scm_empty;
	    break;
	  }
	case 16:
	  {
	    fprintf(stderr, "Ce n'est plus suppose etre utilise!\n");
	    break;
	  }
	case 46:
	  {
	    set_cont_pc(eval_cont, eval_pc);
	    /* continue to 17 */
	  }
	case 17:
	  {
	    c_apply(car(eval_args), cdr(eval_args));
	    break;
	  }
	case 18:
	  {
	    fprintf(stderr, "Ce n'est plus suppose etre utilise!\n");
	    break;
	  }
	case 20:
	  {
	    read_bc_info = read_bc_byte;
	    goto label007;
	  }
	case 21:
	  {
	    read_bc_info = read_bc_int;
	  label007:
	    make_normal_frame(read_bc_info());
	    break;
	  }
	case 22:
	  {
	    read_bc_info = read_bc_byte;
	    goto label008;
	  }
	case 23:
	  {
	    read_bc_info = read_bc_int;
	  label008:
	    make_rest_frame(read_bc_info());
	    break;
	  }
	case 24:
	  {
	    return;
	    break;
	  }
	case 26:
	  {
	    eval_val = eval_args;
	    eval_args = car(eval_prev_args);
	    eval_prev_args = cdr(eval_prev_args);
	    set_cdr(eval_val, eval_args);
	    eval_args = eval_val;
	    break;
	  }
	case 27:
	  {
	    push_arg(scm_empty);
	    break;
	  }
	case 28:
	  {
	    push_arg(scm_false);
	    break;
	  }
	case 29:
	  {
	    push_arg(scm_true);
	    break;
	  }
	case 30:
	  {
	    push_arg(TO_SCM_CHAR(read_bc_byte()));
	    break;
	  }
	case 31:
	  {
	    read_bc_info = read_bc_byte;
	    goto label009;
	  }
	case 32:
	  {
	    read_bc_info = read_bc_byte;
	    goto label010;
	  }
	case 33:
	  {
	    read_bc_info = read_bc_int;
	  label009:
	    push_arg(TO_SCM_NUMBER(read_bc_info()));
	    break;
	  }
	case 34:
	  {
	    read_bc_info = read_bc_int;
	  label010:
	    push_arg(TO_SCM_NUMBER(-read_bc_info()));
	    break;
	  }
	case 35:
	  {
	    eval_env = get_frame(1);
	    break;
	  }
	case 36:
	  {
	    frameno = 0;
	    offsetno = 0;
	    goto label011;
	  }
	case 37:
	  {
	    frameno = 0;
	    offsetno = 1;
	    goto label011;
	  }
	case 38:
	  {
	    frameno = 0;
	    offsetno = 2;
	    goto label011;
	  }
	case 39:
	  {
	    frameno = 1;
	    offsetno = 0;
	    goto label011;
	  }
	case 40:
	  {
	    frameno = 1;
	    offsetno = 1;
	    goto label011;
	  }
	case 41:
	  {
	    frameno = 2;
	    offsetno = 0;
	  label011:
	    push_arg(get_var(frameno, offsetno));
	    break;
	  }
	case 42:
	  {
	    make_normal_frame(1);
	    break;
	  }
	case 43:
	  {
	    make_normal_frame(2);
	    break;
	  }
	case 44:
	  {
	    make_rest_frame(1);
	    break;
	  }
	case 45:
	  {
	    eval_cont = make_cont();
	    eval_args = scm_empty;
	    break;
	  }
	case 47:
	  {
	    fprintf(stderr, "Ce n'est plus suppose etre utilise!\n");
	    break;
	  }
	case 48:
	  {
	    dest = read_bc_int();
	    push_arg(make_closure(eval_pc, eval_env));
	    eval_pc = dest;
	    break;
	  }
	case 49:
	  {
	    read_bc_info = read_bc_byte;
	    goto label012;
	  }
	case 50:
	  {
	    read_bc_info = read_bc_int;
	  label012:
	    pop_n_args(read_bc_info());
	    break;
	  }
	case 51:
	  {
	    pop_arg();
	    break;
	  }
	case 54:
	  {
	    set_cont_pc(eval_cont, eval_pc + 1);
	    /* continue to 52 */
	  }
	case 52:
	  {
	    read_bc_info = read_bc_byte;
	    goto label013;
	  }
	case 55:
	  {
	    set_cont_pc(eval_cont, eval_pc + 2);
	    /* continue to 53 */
	  }
	case 53:
	  {
	    read_bc_info = read_bc_int;
	  label013:
	    dest = scm_globs[read_bc_info()];
	    c_apply(dest, eval_args);
	    break;
	  }
	default:
	  {
	    push_arg(apply_cprim(255 - op, eval_args));
	    break;
	  }
	}
    }
}




/* Le programme principal --------------------------------------- */

int init_scm_glob_1(int code)
{
  if (code == -1)      /* Sans valeur initiale */
    return scm_false;
  else if (code < 0)   /* Cprim */
    return C_MAKE_CPRIM(-2 - code);
  else                 /* Fermeture */
    return TO_SCM_NUMBER(code);
}

int init_scm_glob_2(int code)
{
  int entry;

  if (C_PRED_NUMBER(code))
    {
      entry = code >> 1;  /* Et non pas to_c_number(code) */
      return make_closure(entry, scm_empty);
    }
  else
    return code;
}

int main(int argc, char *argv[])
{
  int i;

  if ((1 << LOGCPI) != CHARSPERINT)
    {
      fprintf(stderr, "Verifier LOGCPI.");
      exit(1);
    }

  alloc_heap(DEFAULTHEAPSIZE);

  /* Attention, l'ordre est important! GC, scm_false, etc. */
  scm_false = FALSEVAL;
  for (i=0 ; i<NBGLOBS ; i++)
    globs[i] = scm_false;
  scm_empty = NULLVAL;
  scm_true = TRUEVAL;
  eval_prev_args = scm_empty;

  for (i=0 ; i<nb_scm_globs ; i++)  /* Temporairement */
    scm_globs[i] = init_scm_glob_1(scm_globs[i]);

  nb_symbols = 0;
  scm_symbol_names = c_make_vector(1);
  scm_constants = to_scm_string(const_desc, const_desc_len);

  for (i=0 ; i<nb_scm_globs ; i++)
    scm_globs[i] = init_scm_glob_2(scm_globs[i]);

  intro_state = 0;
  look_ahead_valide = FALSE;

  execute_bc();
  return 0;
}

/* Ajuster la limite de taille du bytecode dans "analyse.scm" */
