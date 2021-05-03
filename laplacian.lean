/-
Copyright (c) 2021 Gabriel Moise. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Moise.
-/

import algebra.big_operators.basic
import combinatorics.simple_graph.adj_matrix
import combinatorics.simple_graph.basic
import linear_algebra.matrix
import project.incidence

/-!
# Laplacian matrices

This module defines the Laplacian matrix `laplace_matrix` of an undirected graph `simple_graph` and
provides theorems and lemmas connecting graph properties to computational properties of the matrix.

## Main definitions

* `laplace_matrix` is the Laplace matrix of a `simple_graph` with coefficients in a ring R
* `degree_matrix` is the degree matrix of a `simple_graph` with coefficients in a ring R
* `signless_laplace_matrix` is the signless Laplace matrix of a `simple_graph` with coefficients in a ring R
* `edge_from_vertices` is the edge that is created by two adjacent vertices

## Main statements

1. The degree of a vertex v is equal to the sum of elements from row v of the adjacency matrix.
2. The Laplacian matrix is symmetric.
3. The sum of elements on any row of the Laplacian is zero.
4. The Laplacian matrix is equal to the difference between the degree and adjancency matrices.
5. The signless Laplacian matrix decomposition.
6. The Laplacian matrix decomposition.
7. The Laplacian is a quadratic form : xᵀ ⬝ L ⬝ x = ∑ e : G.edge_set, (x head(e) - x tail(e)) ^ 2.
-/

open_locale big_operators matrix
open finset matrix simple_graph

universes u v
variables {V : Type u} [fintype V] [decidable_eq V]
variables {R : Type v} [comm_ring R] [nontrivial R] [decidable_eq R]

lemma dot_product_helper {x y z : V → R} (H_eq : x = y) : dot_product x z = dot_product y z :=
by rw H_eq

namespace simple_graph

variables (G : simple_graph V) (R) [decidable_rel G.adj]

lemma adj_matrix_eq {i j : V} (H_eq : i = j) : G.adj_matrix R i j = 0 :=
by simp only [H_eq, irrefl, if_false, adj_matrix_apply]

lemma adj_matrix_adj {i j : V} (H_adj : G.adj i j) : G.adj_matrix R i j = 1 :=
by simp only [H_adj, adj_matrix_apply, if_true]

lemma adj_matrix_not_adj {i j : V} (H_not_adj : ¬ G.adj i j) : G.adj_matrix R i j = 0 :=
by simp only [H_not_adj, adj_matrix_apply, if_false]

-- 1. The degree of a vertex v is equal to the sum of elements from row v of the adjacency matrix.
lemma degree_eq_sum_of_adj_matrix_row {α : Type*} [semiring α] {i : V} :
  (G.degree i : α) = ∑ (j : V), G.adj_matrix α i j :=
by { rw [← mul_one (G.degree i : α)],
     simp only [← adj_matrix_mul_vec_const_apply, mul_vec, dot_product, boole_mul, adj_matrix_apply] }

-- ## Laplacian matrix L

/-- `laplace_matrix G` is the matrix `L` of an `simple graph G` with `∀ i j ∈ V` :
` | L i j = G.degree i`, if `i = j`
` | L i j = - A i j`, otherwise. -/
def laplace_matrix : matrix V V R
| i j := if i = j then G.degree i else - G.adj_matrix R i j

@[simp]
lemma laplace_matrix_apply {i j : V} :
  G.laplace_matrix R i j = if i = j then G.degree i else - G.adj_matrix R i j := rfl

lemma laplace_matrix_eq {i j : V} (H_eq : i = j) : G.laplace_matrix R i j = G.degree i :=
by { rw [laplace_matrix_apply, adj_matrix_apply], simp only [H_eq, if_true, eq_self_iff_true] }

lemma laplace_matrix_neq {i j : V} (H_neq : i ≠ j) : G.laplace_matrix R i j = - G.adj_matrix R i j :=
by simp only [laplace_matrix_apply, adj_matrix_apply, H_neq, if_false]

-- 2. The Laplacian matrix is symmetric.
@[simp]
lemma transpose_laplace_matrix : (G.laplace_matrix R)ᵀ = G.laplace_matrix R :=
begin
  ext i j,
  by_cases H : (i = j),
  { simp only [H, transpose_apply] },
  { rw [transpose_apply, G.laplace_matrix_neq R H, G.laplace_matrix_neq R (ne.symm H)],
    simp [edge_symm] }
end

lemma filter_eq_neq_empty {i : V} [decidable_eq V] : filter (eq i) (univ \ {i}) = ∅ :=
by { ext, tidy }

lemma filter_id {i : V}: filter (λ (x : V), ¬i = x) (univ \ {i}) = (univ \ {i}) :=
by { ext, tidy }

-- 3. The sum of elements on any row of the Laplacian is zero.
lemma sum_of_laplace_row_equals_zero {i : V} : ∑ (j : V), G.laplace_matrix R i j = 0 :=
begin
  rw [sum_eq_add_sum_diff_singleton (mem_univ i), laplace_matrix_eq],
  simp only [laplace_matrix_apply, sum_ite, filter_eq_neq_empty, filter_id, adj_matrix_apply],
  rw [sum_neg_distrib, sum_boole, sum_const, card_empty, zero_smul, zero_add],
  rw degree_eq_sum_of_adj_matrix_row,
  have H : filter (λ (x : V), G.adj i x) (univ \ {i}) = filter (G.adj i) univ,
  { ext,
    simp only [true_and, mem_filter, mem_sdiff, and_iff_right_iff_imp, mem_univ, mem_singleton],
    intro hyp,
    exact ne.symm (G.ne_of_adj hyp) },
  simp only [H, adj_matrix_apply, sum_boole, add_right_neg, eq_self_iff_true],
end

-- ## Degree matrix D

/-- `degree_matrix G` is the matrix `D` with `∀ i j ∈ V` :
` | D i j = 0` if `i` ≠ `j`
` | D i j = G.degree i` otherwise. -/
def degree_matrix : matrix V V R
| i j := if i = j then G.degree i else 0

@[simp]
lemma degree_matrix_apply {i j : V} :
  G.degree_matrix R i j = if i = j then G.degree i else 0 := rfl

lemma degree_matrix_eq {i j : V} (H_eq : i = j) : G.degree_matrix R i j = G.degree i :=
by { rw H_eq, simp only [degree_matrix_apply, if_true, eq_self_iff_true] }

lemma degree_matrix_neq {i j : V} (H_neq : i ≠ j) : G.degree_matrix R i j = 0 :=
by simp only [degree_matrix_apply, H_neq, if_false]

-- 4. L = D - A.
lemma laplace_eq_degree_minus_adj :
  G.laplace_matrix R = G.degree_matrix R - G.adj_matrix R :=
begin
  ext,
  by_cases H : (i = j),
  { rw [G.laplace_matrix_eq R H, dmatrix.sub_apply, G.degree_matrix_eq R H,
        G.adj_matrix_eq R H, sub_zero] },
  { rw [G.laplace_matrix_neq R H, dmatrix.sub_apply, G.degree_matrix_neq R H, zero_sub] }
end

-- ## Signless Laplace matrix Q

def signless_laplace_matrix : matrix V V R := G.degree_matrix R + G.adj_matrix R

@[simp]
lemma signless_laplace_matrix_apply {i j : V} :
  G.signless_laplace_matrix R i j = (G.degree_matrix R + G.adj_matrix R) i j := rfl

-- 5. Q = M ⬝ Mᵀ.
lemma signless_laplace_decomposition : G.signless_laplace_matrix R = G.inc_matrix R ⬝ (G.inc_matrix R)ᵀ :=
begin
  ext,
  by_cases H_ij : i = j,
  { rw [signless_laplace_matrix_apply, dmatrix.add_apply, G.adj_matrix_eq R H_ij, add_zero],
    rw [mul_apply, G.degree_matrix_eq R H_ij, H_ij, degree_equals_sum_of_incidence_row],
    simp only [transpose_apply, inc_matrix_element_power_id] },
  { rw [signless_laplace_matrix_apply, dmatrix.add_apply, G.degree_matrix_neq R H_ij, zero_add],
    rw [mul_apply],
    by_cases H_adj : G.adj i j,
    { simp only [G.adj_matrix_adj R H_adj, transpose_apply, G.adj_sum_of_prod_inc_one R H_adj] },
    { simp only [G.adj_matrix_not_adj R H_adj, transpose_apply,
                 G.inc_matrix_prod_non_adj R H_ij H_adj, sum_const_zero] } }
end

def edge_from_vertices (i j : V) (H_adj : G.adj i j) : G.edge_set := ⟨⟦(i, j)⟧, G.mem_edge_set.mpr H_adj⟩

@[simp]
lemma edge_from_vertices_iff {i j : V} {e : G.edge_set} (H_adj : G.adj i j) :
   e = G.edge_from_vertices i j H_adj ↔ e.val = ⟦(i, j)⟧ :=
begin
  split,
  { intro hyp, simp only [edge_from_vertices, hyp] },
  { intro hyp, tidy }
end

-- 6. L = N(o) ⬝ N(o)ᵀ, for any orientation o.
lemma laplace_decomposition (o : orientation G) :
  G.laplace_matrix R = G.dir_inc_matrix R o ⬝ (G.dir_inc_matrix R o)ᵀ :=
begin
  ext i j,
  by_cases H_ij : i = j,
  { rw [G.laplace_matrix_eq R H_ij, mul_apply, H_ij, G.degree_equals_sum_of_incidence_row R],
    simp only [transpose_apply, G.dir_inc_matrix_elem_squared R] },
  { rw [G.laplace_matrix_neq R H_ij, mul_apply],
    by_cases H_adj : G.adj i j,
    { simp only [G.adj_matrix_adj R H_adj, transpose_apply, G.dir_inc_matrix_prod_of_adj R H_adj],
      have key : ∀ (e : G.edge_set), ite (e.val = ⟦(i, j)⟧) (-1 : R) 0 = - ite (e.val = ⟦(i, j)⟧) 1 0,
      { intro e,
        convert (apply_ite (λ x : R, -x) (e.val = ⟦(i, j)⟧) (1 : R) (0 : R)).symm,
        rw neg_zero },
      have sum : ∑ (e : G.edge_set), ite (e.val = ⟦(i, j)⟧) (-1 : R) 0 =
                 ∑ (e : G.edge_set), - ite (e.val = ⟦(i, j)⟧) (1 : R) 0,
      { simp only [key] },
      rw [sum, sum_hom, neg_inj, sum_boole],
      have key : filter (λ (e : G.edge_set), e.val = ⟦(i, j)⟧) univ = {G.edge_from_vertices i j H_adj},
      { ext,
        simp only [true_and, mem_filter, mem_univ, mem_singleton],
        rw G.edge_from_vertices_iff H_adj },
      rw key,
      simp only [nat.cast_one, card_singleton] },
    { simp only [G.adj_matrix_not_adj R H_adj, transpose_apply,
                 G.dir_inc_matrix_prod_non_adj R H_ij H_adj, sum_const_zero, neg_zero] } }
end

-- 7. The Laplacian is a quadratic form : xᵀ ⬝ L ⬝ x = ∑ e : G.edge_set, (x head(e) - x tail(e)) ^ 2.
lemma laplace_quadratic_form {o : orientation G} (x : V → R) :
  dot_product (vec_mul x (G.laplace_matrix R)) x = ∑ e : G.edge_set, (x (o.head e) - x (o.tail e)) ^ 2 :=
by calc dot_product (vec_mul x (G.laplace_matrix R)) x
       = dot_product (vec_mul x (G.dir_inc_matrix R o ⬝ (G.dir_inc_matrix R o)ᵀ)) x :
   by { rw laplace_decomposition }                          -- xᵀ ⬝ L ⬝ x = xᵀ ⬝ (N ⬝ Nᵀ) ⬝ x
   ... = dot_product (vec_mul (vec_mul x (G.dir_inc_matrix R o)) (G.dir_inc_matrix R o)ᵀ) x :
   by { rw ← vec_mul_vec_mul }                                     -- ... = (xᵀ ⬝ N) ⬝ Nᵀ ⬝ x
   ... = dot_product (λ j, dot_product (vec_mul x (G.dir_inc_matrix R o)) (λ i, (G.dir_inc_matrix R o)ᵀ i j)) x :
   by { apply dot_product_helper, ext, unfold vec_mul }
   ... = dot_product (vec_mul x (G.dir_inc_matrix R o)) (λ (e : G.edge_set), dot_product ((G.dir_inc_matrix R o)ᵀ e) x) :
   by { rw dot_product_assoc }
   ... = dot_product (vec_mul x (G.dir_inc_matrix R o)) ((G.dir_inc_matrix R o)ᵀ.mul_vec x) :
   by { exact dot_product_helper rfl, }                            -- ... = (xᵀ ⬝ N) ⬝ (Nᵀ ⬝ x)
   ... = dot_product (vec_mul x (G.dir_inc_matrix R o)) (vec_mul x (G.dir_inc_matrix R o)) :
   by { rw mul_vec_transpose }                                     -- ... = (xᵀ ⬝ N) ⬝ (xᵀ ⬝ N)ᵀ
   ... = ∑ e : G.edge_set, (x (o.head e) - x (o.tail e)) ^ 2 :
   by { simp only [dot_product, vec_mul_dir_inc_matrix], ring_nf } -- = ∑ e, (x head(e) - x tail(e)) ^ 2

end simple_graph
