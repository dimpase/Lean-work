/-
Copyright (c) 2021 Gabriel Moise. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Moise.
-/

import data.complex.basic
import data.complex.module
import data.fintype.basic
import data.real.basic
import linear_algebra.matrix

/-!
# Symmetric Matrices

This module defines symmetric matrices, together with key properties about their eigenvalues & eigenvectors.
It uses a more restrictive definition of eigenvalues & eigenvectors, together with helping lemmas for vector-matrix 
operations and tools for complex numbers/vectors.

## General definitions

* `vec_conj x` - the complex conjugate of a complex vector `x`
* `vec_re x` - the vector containing the real parts of elements from x
* `vec_im x` - the vector containing the imaginary part of elements from x

## Matrix definitions

* `has_eigenpair M μ x` - `M` has non-zero eigenvector `x` with corresponding eigenvalue `μ`
* `has_eigenvector M x` - `M` has non-zero eigenvector `x`
* `has_eigenvalue M μ`  - `M` has eigenvalue `μ`
* `symm_matrix M` - `M` is a symmetric matrix

## Matrix theorems
1. If x is an eigenvector of matrix M, then a • x is an eigenvector of M, for any non-zero a : ℂ 
2. If there are two eigenvectors of M that have the same correspoding eigenvalue, then any linear combination of them
is also an eigenvector of M with the same eigenvalue μ.

## Symmetric matrix theorems
1. All eigenvalues of a symmetric real matrix M are real.
2. For every real eigenvalue of a symmetric matrix M, there exists a corresponding real-valued eigenvector.
3. If v and w are eigenvectors of a symmetric matrix M with different eigenvalues, then v and w are orthogonal.
-/

open_locale matrix big_operators
open fintype finset matrix complex

universes u v
variables {V : Type u} [fintype V] [decidable_eq V] [nonempty V]
variables {R : Type v} [ring R]

-- ## General lemmas

@[simp]
lemma vec_eq_unfold (x y : V → R) : (λ (i : V), x i) = (λ (i : V), y i) ↔ ∀ (i : V), x i = y i := 
begin
  split, {intros hyp i, exact congr_fun hyp i},
  {intro hyp, ext i; simp[hyp]} 
end

-- x = y ↔ ∀ i, x i = y i
lemma vec_eq_unfold' (x y : V → R) : x = y ↔ ∀ (i : V), x i = y i :=
begin
  split, {intros hyp i, rw hyp},
  {intro hyp, ext i, simp[hyp]},
end

-- yᵀ (M x) = (yᵀ M) x
lemma vec_mul_mul_vec_assoc (M : matrix V V R) (x y : V → R) : dot_product y (mul_vec M x) = dot_product (vec_mul y M) x :=
begin
  have key : vec_mul y M =  λ j, dot_product y (λ i, M i j), {ext j; unfold vec_mul},
  rw [key, dot_product_assoc y M x],
  simp[mul_vec, dot_product],
end

-- ## Coercions
instance : has_coe (V → ℝ) (V → ℂ) := ⟨λ x, (λ i, ⟨x i, 0⟩)⟩
instance : has_coe (matrix V V ℝ) (matrix V V ℂ) := ⟨λ M, (λ i j, ⟨M i j, 0⟩)⟩

-- ## Lemmas on ℂ

lemma sum_complex_re {x : V → ℂ} : (∑ i : V, x i).re = ∑ i : V, (x i).re := by exact linear_map.re.map_sum

lemma sum_complex_im {x : V → ℂ} : (∑ i : V, x i).im = ∑ i : V, (x i).im := by exact linear_map.im.map_sum

-- could not turn ℂ into general R
-- M (a • x) = a • (M x)
lemma mul_vec_smul_assoc (M : matrix V V ℂ) (x : V → ℂ) (a : ℂ) : M.mul_vec (a • x) = a • (M.mul_vec x) :=
begin
  rw ← smul_mul_vec_assoc M x a,
  ext i; 
  {
    simp[mul_vec, dot_product], repeat{rw sum_complex_re}, repeat{rw sum_complex_im}, 
    have key : ∀ (j : V), M i j * (a * x j) = a * M i j * x j, 
    {intro j, rw ← mul_assoc (M i j) a (x j), rw mul_comm (M i j) a},
    simp[key],
  },
end

-- could not turn ℂ into R
-- xᵀ M = (Mᵀ x)ᵀ
lemma vec_mul_to_mul_vec (M : matrix V V ℂ) (x : V → ℂ) : vec_mul x M = mul_vec Mᵀ x := 
begin
  ext i; simp[vec_mul, mul_vec, dot_product];
  simp[sum_complex_re, sum_complex_im, mul_comm],
end

@[simp]
lemma vec_smul_zero (a : ℂ) (x : V → ℂ) : a • x = 0 ↔ a = 0 ∨ x = 0 :=
begin
  split, 
  {
    intro hyp,
    have key : ∀ (i : V), (a • x) i = 0, {intro i, simp[hyp]},
    by_cases H_a : a = 0, {left, assumption},
    {
      right, ext i;
      {
        specialize key i,
        simp at key,
        cases key with key_a key_x, {exfalso, exact H_a key_a},
        simp[key_x],
      }
    }
  },
  {intro hyp, cases hyp with H_a H_x, simp[H_a], simp[H_x]},
end  

-- ## vec_conj
def vec_conj (x : V → ℂ) : V → ℂ := λ i : V, conj (x i)

-- (μ x)* = μ* x*
@[simp]
lemma smul_vec_conj (μ : ℂ) (x : V → ℂ) : vec_conj (μ • x) = (conj μ) • (vec_conj x) := by {ext i; simp[vec_conj]}

@[simp]
lemma vec_norm_sq_zero {x : V → ℂ} : dot_product (vec_conj x) x = 0 ↔ x = 0 :=
begin
  split, 
  {
    intro hyp,
    unfold dot_product at hyp,
    simp[vec_conj, mul_comm, mul_conj] at hyp,
    rw complex.ext_iff at hyp,
    cases hyp with hyp_re hyp_im, 
    simp [sum_complex_re] at hyp_re,
    have key : ∑ i in (univ : finset V), norm_sq (x i) = 0 ↔ ∀ i ∈ (univ : finset V), norm_sq(x i) = 0,
    {apply sum_eq_zero_iff_of_nonneg, intros i h_univ, exact norm_sq_nonneg (x i)},
    simp at key, rw key at hyp_re, 
    ext i;
    {specialize hyp_re i, simp[hyp_re]},
  },
  {intro hyp, simp[hyp]},
end

-- x* = y* ↔ x = y
@[simp]
lemma vec_conj_eq_iff {x y : V → ℂ} : vec_conj x = vec_conj y ↔ x = y :=
begin
  split, {intro hyp, simp[vec_conj, conj_inj] at hyp, ext i; {specialize hyp i, rw hyp}},
  {intro hyp, ext i; rw hyp},
end

-- ## vec_re & vec_im
def vec_re (x : V → ℂ) : V → ℝ := λ i : V, (x i).re
def vec_im (x : V → ℂ) : V → ℝ := λ i : V, (x i).im

lemma coe_vec_re (x : V → ℂ) {i : V} : (vec_re x : V → ℂ) i = ((x i).re : ℂ) :=
begin
  simp[vec_re], exact rfl,
end 

-- x + x* = 2 * Re(x) 
lemma vec_add_conj_eq_two_re (x : V → ℂ) : x + vec_conj x = (2 : ℂ) • (vec_re x : V → ℂ) :=
begin
  ext i, {simp[vec_conj, coe_vec_re x], linarith}, {simp[vec_conj, coe_vec_re x]}
end

lemma mul_vec_to_vec_mul (v : V → ℂ) (M : matrix V V ℂ) : mul_vec M v = vec_mul v Mᵀ :=
begin
  ext i; {unfold mul_vec, unfold vec_mul, unfold matrix.transpose, simp[dot_product_comm]},
end

lemma mul_vec_add_distrib (M : matrix V V ℂ) (x y : V → ℂ) : M.mul_vec (x + y) = M.mul_vec x + M.mul_vec y :=
begin
  ext i; simp[mul_vec],
end

namespace matrix
variables (M : matrix V V ℝ)

/--
## Matrix definitions
Let `M` be a square real matrix. An `eigenvector` of `M` is a complex vector such that `M x = μ x` for some complex number `μ`. 
`μ` is called the `eigenvalue` of `M` corresponding to `eigenvector` `x`.
-/
def has_eigenpair (μ : ℂ) (x : V → ℂ) : Prop := 
  x ≠ 0 ∧ (mul_vec ↑M x = μ • x) 

def has_eigenvector (x : V → ℂ) : Prop := 
  ∃ μ : ℂ, has_eigenpair M μ x

def has_eigenvalue (μ : ℂ) : Prop :=
  ∃ x : V → ℂ, has_eigenpair M μ x

def symm_matrix : Prop := M = Mᵀ

-- ## Matrix : Helping lemmas

-- (↑M)ᵀ = ↑Mᵀ
lemma coe_transpose_matrix (M : matrix V V ℝ) : (↑M : matrix V V ℂ)ᵀ = (↑(Mᵀ) : matrix V V ℂ) :=
begin
  ext i j, tidy, 
end

-- ↑M i j = ↑(M i j)
lemma coe_matrix_coe_elem (i j : V) : (M : matrix V V ℂ) i j = ↑(M i j) := by exact rfl

-- (M x)* = M x*
lemma vec_conj_mul_vec (x : V → ℂ) : vec_conj (mul_vec ↑M x) = mul_vec (↑M : matrix V V ℂ) (vec_conj x) :=
begin
  ext i;
  simp[vec_conj, mul_vec, dot_product, coe_matrix_coe_elem],
  {simp[sum_complex_re]}, {simp[sum_complex_im]},
end

-- ## Matrix : Theorems

-- ### 1. If x is an eigenvector of M, then a • x is an eigenvector of M, for any non-zero a : ℂ 

theorem eigenvector_smul_eigenvector (a : ℂ) (x : V → ℂ) (H_na : a ≠ 0) (H_eigenvector : has_eigenvector M x) :
  has_eigenvector M (a • x) :=
begin
  rcases H_eigenvector with ⟨μ, ⟨H_nx, H_mul⟩⟩,
  use μ,
  split, {intro hyp, rw vec_smul_zero a x at hyp, tauto},
  {simp[mul_vec_smul_assoc (M : matrix V V ℂ) x a, H_mul, smul_smul, mul_comm]},
end

-- ### 2. If there are two eigenvectors that have the same correspoding eigenvalue, then any linear combination of them
-- ### is also an eigenvector with the same eigenvalue μ.
theorem linear_combination_eigenvectors (a b : ℂ) (v w : V → ℂ) (μ : ℂ) (H_ne : a • v + b • w ≠ 0) 
(H₁ : has_eigenpair M μ v) (H₂ : has_eigenpair M μ w) : has_eigenpair M μ (a • v + b • w) :=
begin
  cases H₁ with H₁₁ H₁₂, cases H₂ with H₂₁ H₂₂,
  unfold has_eigenpair,
  split, {exact H_ne},
  {
    have h₁ : mul_vec (M : matrix V V ℂ) (a • v + b • w) = mul_vec (M : matrix V V ℂ) (a • v) + mul_vec (M : matrix V V ℂ) (b • w), 
    {ext i; simp[mul_vec]},
    rw h₁, clear h₁,
    have h₂ : mul_vec (M : matrix V V ℂ) (a • v) = a • (mul_vec (M : matrix V V ℂ) v), {ext i; simp[mul_vec]},
    have h₃ : mul_vec (M : matrix V V ℂ) (b • w) = b • (mul_vec (M : matrix V V ℂ) w), {ext i; simp[mul_vec]},
    rw [h₂, h₃], clear h₂, clear h₃,
    rw [H₁₂, H₂₂],
    have h₄ : μ • (a • v + b • w) = μ • (a • v) + μ • (b • w), {simp},
    rw h₄, clear h₄,
    simp[smul_smul, mul_comm],
  },
end

-- ## Symmetric matrix : Theorems

lemma symm_matrix_def (H_symm : symm_matrix M): M = Mᵀ := by assumption
lemma symm_matrix_elems (H_symm : symm_matrix M) (i j : V) : M i j = M j i := by tidy

lemma symmetric_matrix_coe (H_symm : symm_matrix M) : (M : matrix V V ℂ) = (M : matrix V V ℂ)ᵀ :=
begin
  rw coe_transpose_matrix,
  unfold symm_matrix at H_symm,
  rw ← H_symm,
end

-- vᵀ (M w) = (vᵀ M)ᵀ w 
lemma mul_vec_vec_mul (v w : V → ℂ) : 
  dot_product v (mul_vec (M : matrix V V ℂ) w) = dot_product (vec_mul v (M : matrix V V ℂ)) w :=
begin
  have key : vec_mul v (M : matrix V V ℂ) = (λ j, dot_product v (λ i, (M : matrix V V ℂ) i j)), 
  {ext j; unfold vec_mul},
  rw key,
  rw dot_product_assoc v (M : matrix V V ℂ) w,
  have key : (mul_vec (M : matrix V V ℂ) w) = (λ (i : V), dot_product ((M : matrix V V ℂ) i) w), {ext i; unfold mul_vec,},
  rw key,
end

/--
### 1. All eigenvalues of a symmetric real matrix M are real.
(following the proof from https://www.doc.ic.ac.uk/~ae/papers/lecture05.pdf)
-/

theorem symm_matrix_real_eigenvalues (H_symm : symm_matrix M) : ∀ (μ : ℂ), has_eigenvalue M μ → μ.im = 0 :=
begin
  -- Let μ ∈ ℂ be an eigenvalue of a symmetric matrix M ∈ ℝⁿˣⁿ, and x ∈ ℂⁿ be a corresponding (non-zero) eigenvector
  -- (1) M x = μ x
  rintro μ ⟨x, ⟨H_x, H_eq₁⟩⟩,
  -- (2) M x* = μ* x*
  have H_eq₂ : mul_vec ↑M (vec_conj x) =  (conj μ) • (vec_conj x), 
  {rw [← smul_vec_conj μ x, ← M.vec_conj_mul_vec x, H_eq₁]},
  -- (3) μ ((x*)ᵀ x) = μ* ((x*)ᵀ x)
  have H_eq₃ : μ * (dot_product (vec_conj x) x) = conj μ * dot_product (vec_conj x) x,

  calc μ * dot_product (vec_conj x) x = dot_product (vec_conj x) (μ • x) :                -- μ ((x*)ᵀ x) = (x*)ᵀ (μ x) 
          by {rw ← smul_dot_product μ (vec_conj x) x, simp[dot_product, vec_conj, dot_product, ← mul_assoc, mul_comm]} 
                                  ... = dot_product (vec_conj x) ((M : matrix V V ℂ).mul_vec x) : -- ... = (x*)ᵀ (M x)
          by {rw ← H_eq₁}
                                  ... = dot_product ((M : matrix V V ℂ).vec_mul (vec_conj x)) x : -- ... = ((x*)ᵀ M) x
          by {exact vec_mul_mul_vec_assoc ↑M x (vec_conj x)}
                                  ... = dot_product ((↑M)ᵀ.mul_vec (vec_conj x)) x :              -- ... = (Mᵀ x*)ᵀ x
          by {rw vec_mul_to_mul_vec (M : matrix V V ℂ) (vec_conj x)}
                                  ... = dot_product ((M : matrix V V ℂ).mul_vec (vec_conj x)) x : -- ... = (M x*)ᵀ x
          by {have H : (M : matrix V V ℂ) = (M : matrix V V ℂ)ᵀ, {tidy}, rw ← H} 
                                  ... = dot_product (conj μ • vec_conj x) x :                     -- ... = (μ* x*)ᵀ x
          by {rw H_eq₂}
                                  ... = conj μ * dot_product (vec_conj x) x :                     -- ... = μ* ((x*)ᵀ x)           
          by {rw ← smul_dot_product (conj μ) (vec_conj x) x},
  
  -- (4) (μ - μ*) ((x*)ᵀ x) = 0
  have H_eq₄ : (μ - conj μ) * dot_product (vec_conj x) x = 0, 
  {rw sub_mul μ (conj μ) (dot_product (vec_conj x) x), simp[H_eq₃]},
  -- μ - μ* = 0 ∨ (x*)ᵀ x = 0
  rw mul_eq_zero at H_eq₄,
  cases H_eq₄ with H_μ H_prod,
  { -- μ - μ* = 0
    rw [sub_eq_zero, eq_comm, eq_conj_iff_real] at H_μ,
    cases H_μ with r H_r, rw H_r,
    refl },
  { -- (x*)ᵀ x = 0
    exfalso,
    exact H_x (vec_norm_sq_zero.mp H_prod) },
end

/--
### 2. For every real eigenvalue of a symmetric matrix M, there exists a corresponding real-valued eigenvector.
(following the proof from https://sharmaeklavya2.github.io/theoremdep/nodes/linear-algebra/eigenvectors/real-matrix-with-real-eigenvalue-has-real-eigenvectors.html)
-/
theorem symm_matrix_real_eigenvectors (H_symm : symm_matrix M) (μ : ℂ) (H_eigenvalue : has_eigenvalue M μ) : 
  ∃ x_real : V → ℂ, has_eigenpair M μ x_real ∧ vec_im (x_real) = 0 :=
begin
  -- We know that μ ∈ ℝ from previous theorem that μ ∈ ℝ.
  have H_μ : ∀ (μ : ℂ), has_eigenvalue M μ → μ.im = 0, {exact M.symm_matrix_real_eigenvalues H_symm},
  specialize H_μ μ, simp[H_eigenvalue] at H_μ, 
  rcases H_eigenvalue with ⟨x, ⟨H_nx, H_mul⟩⟩,
  by_cases H_re : vec_re x = 0,
  { -- x = I • x', for some x' ∈ ℝⁿ, therefore I • x ∈ ℝⁿ and will be the chosen real eigenvector 
    use (I • x),
    split,
    { -- I • x is an eigenvector
      split, 
      {intro hyp, rw vec_smul_zero I x at hyp, have H_nI : I ≠ 0, {exact I_ne_zero}, tauto}, -- I • x ≠ 0
      {simp[mul_vec_smul_assoc, H_mul, smul_smul, mul_comm]} -- M (I • x) = μ • (I • x)
    },
    { -- I • x ∈ ℝⁿ
      ext i,
      simp[vec_re, vec_im] at *, specialize H_re i,
      exact H_re 
    }
  },
  { -- x + x* will be used according to the linked proof
    use (x + vec_conj x),
    split,
    { -- x + x* is an eigenvector
      split,
      { -- x + x* ≠ 0
        rw vec_add_conj_eq_two_re x, intro hyp, rw vec_smul_zero at hyp,
        cases hyp with H_20 H_x, {simp[complex.ext_iff] at H_20, linarith}, -- 2 ≠ 0
        { -- vec_re x ≠ 0
          rw vec_eq_unfold' at H_x, 
          apply H_re, 
          ext i, specialize H_x i, 
          rw coe_vec_re at H_x, 
          simp at H_x, simp[vec_re, H_x],
        }
      },
      { -- M (x + x*) = μ (x + x*)
        have H_mul' : vec_conj ((M : matrix V V ℂ).mul_vec x) = vec_conj (μ • x), -- (M x)* = (μ x)*
        {exact vec_conj_eq_iff.mpr H_mul}, 
        rw M.vec_conj_mul_vec x at H_mul', -- M x* = (μ x)*
        rw smul_vec_conj at H_mul', -- M x* = μ* x*
        have H_conj : conj μ = μ, {ext; {simp[H_μ]}},
        rw H_conj at H_mul', clear H_conj, -- M x* = μ x*
        simp[mul_vec] at *, intro i, specialize H_mul i, specialize H_mul' i, rw [H_mul, H_mul'],
      },
    },
    { -- x + x* ∈ ℝⁿ
      ext i,
      simp[vec_add_conj_eq_two_re, vec_im, coe_vec_re],
    }
  },
end 

-- ## 3. If v and w are eigenvectors of a symmetric matrix M with different eigenvalues, then v and w are orthogonal.
lemma orthogonal_eigenvectors_if_distinct_eigenvalue (H_symm : symm_matrix M) (v w : V → ℂ) (μ μ' : ℂ)
(H_ne : μ ≠ μ') (H₁ : has_eigenpair M μ v) (H₂ : has_eigenpair M μ' w) : dot_product v w = 0 :=
begin
  have key : (μ - μ') * dot_product v w = 0, 
  calc (μ - μ') * dot_product v w = μ * dot_product v w - μ' * dot_product v w : 
          by {exact mul_sub_right_distrib μ μ' (dot_product v w)} -- (μ - μ') (vᵀ w) = μ (vᵀ w) - μ' (vᵀ w)
                              ... = dot_product (μ • v) w - dot_product v (μ' • w) :         
          by {simp}                                                           -- ... = (μ v)ᵀw - vᵀ (μ' w)
                              ... = dot_product ((M : matrix V V ℂ).mul_vec v) w - dot_product v ((M : matrix V V ℂ).mul_vec w) :
          by {rw [H₁.2, H₂.2]}                                                -- ... = (M v)ᵀ w - vᵀ (M w)
                              ... = dot_product ((M : matrix V V ℂ).mul_vec v) w - dot_product (vec_mul v (M : matrix V V ℂ)) w :
          by {rw M.mul_vec_vec_mul v w}                                       -- ... = (M v)ᵀ w - (vᵀ M)ᵀ w 
                              ... = dot_product ((M : matrix V V ℂ).mul_vec v) w - dot_product (vec_mul v (M : matrix V V ℂ)ᵀ) w :
          by {rw ← symmetric_matrix_coe M H_symm}                             -- ... = (M v)ᵀ w - (vᵀ Mᵀ)ᵀ w
                              ... =  dot_product ((M : matrix V V ℂ).mul_vec v) w - dot_product (mul_vec (M : matrix V V ℂ) v) w :
          by {rw mul_vec_to_vec_mul v (M : matrix V V ℂ)}                     -- ... = (M v)ᵀ w - (M v)ᵀ w
                              ... = 0 :
          by {simp},                                                           -- ... = 0
  simp at key,
  cases key with H_μ H_dot, {exfalso, rw sub_eq_zero_iff_eq at H_μ, exact H_ne H_μ},
  {exact H_dot},
end

-- TODOs :
-- 1. positive semidefinite matrices
-- 2. eigenvalues = roots of characteristic polynomial (char_poly)
-- 3. eigendecomposition of a diagonalizable matrix

end matrix

