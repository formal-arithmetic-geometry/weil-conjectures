/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ArtinSchreier
public import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.FieldTheory.Separable
import Sheaf.AlgebraicGeometry.RelativeSpecBaseChange
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas

/-!
# The trace-polynomial morphism of Artin–Schreier covers

Source: Laumon, Transformation de Fourier (1987), (1.1.3), pp. 139–140, Lang torsor
pushout; the explicit polynomial realization is supplied by the DAG proof
(blueprint: lem-a1-artin-schreier-trace-cover-map).

The covers are the actual pullbacks of the upstream Artin–Schreier map along the section
specified by the function. Thus their affine charts are the displayed polynomial quotients.
The structure below specifies the translations and trace map by their coordinate formulas,
which uniquely determine these morphisms over the base. No maps are chosen arbitrarily.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

/-- The cover `y^n-y=f`, constructed as the pullback of the upstream Artin–Schreier map.
Source: Laumon (1.1.3), pp. 139–140; affine charts as in Stacks 01LX
(blueprint: lem-a1-artin-schreier-trace-cover-map). -/
def artinSchreierFunctionCover (X : Scheme.{u}) (n : ℕ) (f : Γ(X, ⊤)) : Scheme.{u} :=
  pullback (AffineSpace.artinSchreierMap PUnit X n)
    (AffineSpace.homOfVector (𝟙 X) (fun _ : PUnit ↦ f))

/-- The structural projection of `y^n-y=f` to `X`.
Source: Laumon (1.1.3), pp. 139–140
(blueprint: lem-a1-artin-schreier-trace-cover-map). -/
def artinSchreierFunctionProjection (X : Scheme.{u}) (n : ℕ) (f : Γ(X, ⊤)) :
    artinSchreierFunctionCover X n f ⟶ X :=
  pullback.snd _ _

/-- The tautological root `y` on the cover `y^n-y=f`.
Source: the explicit coordinates in the DAG proof of Laumon (1.1.3)
(blueprint: lem-a1-artin-schreier-trace-cover-map). -/
def artinSchreierFunctionRoot (X : Scheme.{u}) (n : ℕ) (f : Γ(X, ⊤)) :
    Γ(artinSchreierFunctionCover X n f, ⊤) :=
  (pullback.fst (AffineSpace.artinSchreierMap PUnit X n)
    (AffineSpace.homOfVector (𝟙 X) (fun _ : PUnit ↦ f))).appTop
      (AffineSpace.coord X PUnit.unit)

/-- A constant from the base field, as a global regular function.
Source: Laumon (0.2), (1.1.3); the given scheme-over-field structure
(blueprint: lem-a1-artin-schreier-trace-cover-map). -/
def artinSchreierBaseConstants (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] : k →+* Γ(X, ⊤) :=
  (X ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- The polynomial `Θ_b = ∑ i < r, (b y)^(p^i)`, over any ring of sections, including zero.
Source: the explicit realization of Laumon (1.1.3) in the DAG proof
(blueprint: lem-a1-artin-schreier-trace-cover-map). -/
def artinSchreierTracePolynomial {A : Type u} [CommRing A] (p r : ℕ) (b : A) : Polynomial A :=
  ∑ i ∈ Finset.range r, (Polynomial.C b * Polynomial.X) ^ (p ^ i)

/-- The canonical map of geometric fibre schemes induced by a morphism over `X`.
Source: base change of the maps in Laumon (1.1.3), Stacks 01LX
(blueprint: lem-a1-artin-schreier-trace-cover-map). -/
def artinSchreierFibreMap {X Y Z T : Scheme.{u}} (π : Y ⟶ X) (ρ : Z ⟶ X)
    (x : T ⟶ X) (a : Y ⟶ Z) (ha : a ≫ ρ = π) : pullback π x ⟶ pullback ρ x :=
  pullback.map π x ρ x a (𝟙 T) (𝟙 X)
    (by simpa only [Category.comp_id] using ha.symm) (by simp)

/-- The canonical translations and trace morphism on the two explicit covers. The fields
`σ_root`, `τ_root`, and `θ_root`, together with being over `X`, uniquely specify the maps.
Source: the coordinate construction in Laumon (1.1.3), pp. 139–140, expanded in the DAG proof
(blueprint: lem-a1-artin-schreier-trace-cover-map). -/
structure ArtinSchreierTraceMaps (k : Type u) [Field k] (p r : ℕ) [Algebra (ZMod p) k]
    (b : k) (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) where
  σ : k → (artinSchreierFunctionCover X (p ^ r) f ≅ artinSchreierFunctionCover X (p ^ r) f)
  τ : ZMod p →
    (artinSchreierFunctionCover X p (artinSchreierBaseConstants k X b * f) ≅
      artinSchreierFunctionCover X p (artinSchreierBaseConstants k X b * f))
  θ : artinSchreierFunctionCover X (p ^ r) f ⟶
    artinSchreierFunctionCover X p (artinSchreierBaseConstants k X b * f)
  σ_over (c : k) : (σ c).hom ≫ artinSchreierFunctionProjection X (p ^ r) f =
    artinSchreierFunctionProjection X (p ^ r) f
  τ_over (d : ZMod p) : (τ d).hom ≫
    artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f) =
      artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f)
  θ_over : θ ≫
    artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f) =
      artinSchreierFunctionProjection X (p ^ r) f
  σ_root (c : k) : (σ c).hom.appTop (artinSchreierFunctionRoot X (p ^ r) f) =
    artinSchreierFunctionRoot X (p ^ r) f +
      (artinSchreierFunctionProjection X (p ^ r) f).appTop (artinSchreierBaseConstants k X c)
  τ_root (d : ZMod p) : (τ d).hom.appTop
    (artinSchreierFunctionRoot X p (artinSchreierBaseConstants k X b * f)) =
      artinSchreierFunctionRoot X p (artinSchreierBaseConstants k X b * f) +
        (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f)).appTop
          (artinSchreierBaseConstants k X (algebraMap (ZMod p) k d))
  θ_root : θ.appTop
    (artinSchreierFunctionRoot X p (artinSchreierBaseConstants k X b * f)) =
      (artinSchreierTracePolynomial p r
        ((artinSchreierFunctionProjection X (p ^ r) f).appTop
          (artinSchreierBaseConstants k X b))).eval (artinSchreierFunctionRoot X (p ^ r) f)
  σ_zero : (σ 0).hom = 𝟙 _
  σ_add (c d : k) : (σ (c + d)).hom = (σ c).hom ≫ (σ d).hom
  τ_zero : (τ 0).hom = 𝟙 _
  τ_add (c d : ZMod p) : (τ (c + d)).hom = (τ c).hom ≫ (τ d).hom

/-- All five assertions for the trace-polynomial morphism of Artin–Schreier covers.
Source: Laumon (1.1.3), pp. 139–140 (Lang torsor pushout), with the explicit construction
and calculations of the DAG proof (blueprint: lem-a1-artin-schreier-trace-cover-map).

Proof:
1. On each affine chart use the monic-quotient basis (lem-weil-pbc-monic-quotient-free).
   The derivative is -1, so the standard-etale presentation is etale
   (lem-weil-pbc-standard-etale-monic-derivative). Relative-Spec charts glue these assertions
   (lem-weil-pbc-affine-morphism-relative-spec); the quotient algebras are quasi-coherent
   (pqf-def-coherent). The identical argument works on empty charts using the zero ring.
2. Relative-Spec base change and the affine-sections formula for module pullback identify
   the quotient after any base change with the same quotient in the new coefficient ring
   (lem-weil-pbc-relative-spec-base-change, lem-weil-pbc-module-pullback-affine-sections).
3. Frobenius and c^q=c preserve the equation under y ↦ y+c; the inverse is y ↦ y-c
   (def-weil-ring-frobenius, lem-weil-finite-field-pow-card). These substitutions glue.
4. On a geometric fibre the separable monic polynomial has q distinct roots
   (def-pc-separable-polynomial, lem-pc-separable-polynomial-distinct-roots-alg-closed).
   If α is one root, the α+c are all its roots. Thus translation is simply transitive.
5. Frobenius telescopes Θ_b^p-Θ_b to (by)^(p^r)-by = b(y^q-y). Reducing by the equation
   gives bf, hence the coordinate substitution t ↦ Θ_b descends and glues to θ.
6. The finite-field trace formula (lem-a1-finite-field-trace-frobenius-sum) identifies
   ∑ (bc)^(p^i) with Tr(bc), since finrank over F_p is r. Hence Θ_b(y+c)=Θ_b(y)+Tr(bc),
   proving equivariance on generators and thus on schemes by the relative-Spec equivalence.
7. The map c ↦ Tr(bc) is F_p-linear and surjective by trace-pairing nondegeneracy
   (lem-a1-trace-pairing-nondegenerate), since b≠0. Its p equal-sized cosets partition k,
   so its kernel has q/p elements. This does not assume Tr(1)≠0.
8. On geometric fibres θ sends α+c to Θ_b(α)+Tr(bc). Surjectivity of trace proves
   surjectivity of θ; equal images are exactly differences in the trace kernel.
9. Every coefficient pullback fixes b, c and the prime-field constants and carries f to h^*f.
   The three displayed substitutions therefore commute with arbitrary base change, on
   coefficients and the coordinate generator, and then globally by relative Spec. The
   comparison squares are cartesian and give the canonical isomorphisms to the pullbacks.
-/
theorem artinSchreier_trace_cover_map (k : Type u) [Field k] [Fintype k]
    (p r : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (hr : 1 ≤ r) (hcard : Fintype.card k = p ^ r) (b : k) (hb : b ≠ 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (f : Γ(X, ⊤)) :
    ∃ M : ArtinSchreierTraceMaps k p r b X f,
      IsFinite (artinSchreierFunctionProjection X (p ^ r) f) ∧
      Etale (artinSchreierFunctionProjection X (p ^ r) f) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Nonempty ↥(pullback (artinSchreierFunctionProjection X (p ^ r) f) x : Scheme.{u}) ∧
        (∀ z z' : ↥(pullback (artinSchreierFunctionProjection X (p ^ r) f) x : Scheme.{u}),
          ∃! c : k, artinSchreierFibreMap _ _ x (M.σ c).hom (M.σ_over c) z = z') ∧
        Nat.card ↥(pullback (artinSchreierFunctionProjection X (p ^ r) f) x : Scheme.{u}) = p ^ r) ∧
      (∀ U : X.Opens,
        artinSchreierTracePolynomial p r
            (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (artinSchreierBaseConstants k X b)) ^ p -
          artinSchreierTracePolynomial p r
            (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (artinSchreierBaseConstants k X b)) =
          Polynomial.C
            (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (artinSchreierBaseConstants k X b)) *
            (Polynomial.X ^ (p ^ r) - Polynomial.X)) ∧
      (∀ U : X.Opens,
        (AdjoinRoot.mk (Polynomial.X ^ (p ^ r) - Polynomial.X -
          Polynomial.C (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f))
          (artinSchreierTracePolynomial p r
            (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
              (artinSchreierBaseConstants k X b)))) ^ p -
        AdjoinRoot.mk (Polynomial.X ^ (p ^ r) - Polynomial.X -
          Polynomial.C (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f))
          (artinSchreierTracePolynomial p r
            (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (artinSchreierBaseConstants k X b))) =
        AdjoinRoot.of (Polynomial.X ^ (p ^ r) - Polynomial.X -
          Polynomial.C (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f))
          (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (artinSchreierBaseConstants k X b) *
            X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f)) ∧
      (∀ c : k, (M.σ c).hom ≫ M.θ =
        M.θ ≫ (M.τ (Algebra.trace (ZMod p) k (b * c))).hom) ∧
      Nat.card {c : k // Algebra.trace (ZMod p) k (b * c) = 0} = p ^ r / p ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Function.Surjective (artinSchreierFibreMap _ _ x M.θ M.θ_over) ∧
        ∀ z z' : ↥(pullback (artinSchreierFunctionProjection X (p ^ r) f) x : Scheme.{u}),
          artinSchreierFibreMap _ _ x M.θ M.θ_over z =
            artinSchreierFibreMap _ _ x M.θ M.θ_over z' ↔
          ∃ c : k, Algebra.trace (ZMod p) k (b * c) = 0 ∧
            artinSchreierFibreMap _ _ x (M.σ c).hom (M.σ_over c) z = z') ∧
      (∀ (X' : Scheme.{u}) [X'.Over (Spec (.of k))]
          [IsSeparated (X' ↘ Spec (.of k))] [LocallyOfFiniteType (X' ↘ Spec (.of k))]
          [QuasiCompact (X' ↘ Spec (.of k))] (h : X' ⟶ X) [h.IsOver (Spec (.of k))],
        ∃ (M' : ArtinSchreierTraceMaps k p r b X' (h.appTop f))
          (uq : artinSchreierFunctionCover X' (p ^ r) (h.appTop f) ⟶
            artinSchreierFunctionCover X (p ^ r) f)
          (up : artinSchreierFunctionCover X' p
              (artinSchreierBaseConstants k X' b * h.appTop f) ⟶
            artinSchreierFunctionCover X p (artinSchreierBaseConstants k X b * f)),
          IsPullback uq (artinSchreierFunctionProjection X' (p ^ r) (h.appTop f))
            (artinSchreierFunctionProjection X (p ^ r) f) h ∧
          IsPullback up (artinSchreierFunctionProjection X' p
              (artinSchreierBaseConstants k X' b * h.appTop f))
            (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f)) h ∧
          uq.appTop (artinSchreierFunctionRoot X (p ^ r) f) =
            artinSchreierFunctionRoot X' (p ^ r) (h.appTop f) ∧
          up.appTop (artinSchreierFunctionRoot X p (artinSchreierBaseConstants k X b * f)) =
            artinSchreierFunctionRoot X' p (artinSchreierBaseConstants k X' b * h.appTop f) ∧
          (∀ c : k, (M'.σ c).hom ≫ uq = uq ≫ (M.σ c).hom) ∧
          (∀ d : ZMod p, (M'.τ d).hom ≫ up = up ≫ (M.τ d).hom) ∧
          M'.θ ≫ up = uq ≫ M.θ) := by
  sorry

end

end AlgebraicGeometry
