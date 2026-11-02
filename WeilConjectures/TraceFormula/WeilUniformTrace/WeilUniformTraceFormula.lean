/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Grothendieck–Lefschetz for condensed Weil complexes

Source: literature/blueprint/latest/blueprint/sec-trace-formula/
sk-thm-tf-uniform-formula/det-thm-tf-uniform-formula-weil.md, clauses (1)--(3)
(blueprint: det-thm-tf-uniform-formula-weil).

All pairs belong to the recorded bounded constructible category of actual condensed
modules. The compact operator is the recorded global geometric Frobenius. Local operators
use derived pullback composition and the geometric-point reparametrization. Scalars are
constant global sections of the coefficient ring, with its canonical ring identification
with the indicated coefficient field. No integral lattice is part of a Weil structure.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.WeilUniformTrace

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

/-- The coefficient ring in its canonical constant-global-section presentation.
Source: the displayed identity in clause (2)
(blueprint: det-thm-tf-uniform-formula-weil). -/
abbrev scalars (c : WeilCoefficient ell) := MonObj.Γ (WeilCoefficient.ab.{u} c)

/-- The specified compact coefficient complex, on the chosen compactification presentation.
Source: clause (1), H_c^i = H^i RΓ_c
(blueprint: det-thm-tf-uniform-formula-weil). -/
abbrev compactComplex (c : WeilCoefficient ell)
    (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ c) :=
  (condensedRingCompactCoefficientComplex (WeilCoefficient.ab c) c₀).obj K.obj.carrier

/-- Cohomology of the specified compact coefficient complex in every integer degree.
Source: clause (1) (blueprint: det-thm-tf-uniform-formula-weil). -/
abbrev compactCohomology (c : WeilCoefficient ell)
    (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ c) (i : ℤ) :=
  (DerivedCategory.homologyFunctor _ i).obj (compactComplex D ell hEll X₀ c c₀ K)

/-- The m-fold Weil map, with the actual derived pullback compositors and identity unitor.
Source: clause (2), theta^[m], and its proof's recurrence
(blueprint: det-thm-tf-uniform-formula-weil). -/
def iterate {T : Scheme.{u}}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (g : End T) {M : CohomologyTransport.D Λ T}
    (θ : (CohomologyTransport.L Λ g).obj M ≅ M) :
    (m : ℕ) → (CohomologyTransport.L Λ (g ^ m)).obj M ≅ M
  | 0 => (leftDerivedUpperStarId Λ T).app M
  | m + 1 =>
    eqToIso (congrArg (fun f : End T ↦ (CohomologyTransport.L Λ f).obj M)
      (pow_succ g m)) ≪≫
      (leftDerivedUpperStarComp Λ g (g ^ m)).app M ≪≫
        (CohomologyTransport.L Λ g).mapIso (iterate Λ g θ m) ≪≫ θ

/-- The geometric point lift has the required structural-map equality.
Source: the geometric point bar y in clause (2)
(blueprint: det-thm-tf-uniform-formula-weil).
Proof: compose the over-point equation of y with Spec k → Spec F_(q^m). The subfield
embedding from the finite-field datum composes with k₀ → F_(q^m) to k₀ → k, by the
unique-subfield theorem's specified embedding equation. Functoriality of Spec gives
exactly the displayed equality. -/
theorem extensionPoint_square (m : ℕ) (hm : 1 ≤ m)
    (y : D.extensionPoints X₀ m hm) :
    (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫ y.left) ≫
        X₀.hom =
      (𝟙 (Spec (.of D.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  sorry

/-- The canonical geometric lift of an extension-valued point, by the fibre product.
Source: clause (2), y and bar y (blueprint: det-thm-tf-uniform-formula-weil). -/
def extensionPoint (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) :
    Spec (.of D.k) ⟶ (D.geometricFiber X₀).left :=
  pullback.lift (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫ y.left)
    (𝟙 _) (extensionPoint_square D X₀ m hm y)

/-- The stalk coefficient complex uses the recorded derived pullback and point sections.
Source: clauses (1)--(3), K_bar y
(blueprint: det-thm-tf-uniform-formula-weil). -/
abbrev stalkComplex (c : WeilCoefficient ell)
    (K : strictWeilComplexCategory D ell hEll X₀ c)
    (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) :=
  (GeometricFrobeniusTransport.pointSections (WeilCoefficient.ab c) (Spec (.of D.k))).obj
    ((CohomologyTransport.L (WeilCoefficient.ab c) (extensionPoint D X₀ m hm y)).obj
      K.obj.carrier)

/-- The stalk's cohomology in every integer degree.
Source: clause (1) (blueprint: det-thm-tf-uniform-formula-weil). -/
abbrev stalkCohomology (c : WeilCoefficient ell)
    (K : strictWeilComplexCategory D ell hEll X₀ c)
    (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) (i : ℤ) :=
  (DerivedCategory.homologyFunctor _ i).obj (stalkComplex D ell hEll X₀ c K m hm y)

/-- The return is semilinear reparametrization, rather than a fixed geometric point map.
Source: clause (2), the m-fold local operator
(blueprint: det-thm-tf-uniform-formula-weil).
Proof: geometric Frobenius to the m-th power fixes F_(q^m) pointwise. Compare the two
projections from X: the model projection is unchanged, while the closure projection
is composed with Spec(gamma)^m. The universal property of the pullback proves the
return equality. -/
theorem point_return (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) :
    extensionPoint D X₀ m hm y ≫ (End.of (D.geometricFrobenius X₀).hom ^ m) =
      (End.of (GeometricFrobeniusTransport.baseAutomorphism D).hom ^ m) ≫
        extensionPoint D X₀ m hm y := by
  sorry

/-- The actual local m-fold return: insert the point reparametrization, apply the
pullback-square comparison, then pull back the m-fold Weil map.
Source: clause (2), F_y,m (blueprint: det-thm-tf-uniform-formula-weil). -/
def localFrobenius (c : WeilCoefficient ell)
    (K : strictWeilComplexCategory D ell hEll X₀ c)
    (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) :
    End (stalkComplex D ell hEll X₀ c K m hm y) := by
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let Λ := WeilCoefficient.ab.{u} c
  let x := extensionPoint D X₀ m hm y
  let g := End.of (D.geometricFrobenius X₀).hom
  let b := End.of (GeometricFrobeniusTransport.baseAutomorphism D).hom
  let θ := (leftDerivedUpperStarIsoMapDerivedCategory Λ g).app K.obj.carrier ≪≫ K.obj.str
  let χ := (leftDerivedUpperStarComp Λ (b ^ m) x).symm.app K.obj.carrier ≪≫
    eqToIso (congrArg (fun f ↦ (CohomologyTransport.L Λ f).obj K.obj.carrier)
      (point_return D X₀ m hm y).symm) ≪≫
      (leftDerivedUpperStarComp Λ x (g ^ m)).app K.obj.carrier
  exact (GeometricFrobeniusTransport.pointInsertion Λ (b ^ m)).hom.app
      ((CohomologyTransport.L Λ x).obj K.obj.carrier) ≫
    (GeometricFrobeniusTransport.pointSections Λ (Spec (.of D.k))).map
      (χ.hom ≫ (CohomologyTransport.L Λ x).map (iterate Λ g θ m).hom)

/-- The global compact Frobenius is precisely the recorded operator of the dependency.
Source: clause (2), F (blueprint: det-thm-tf-uniform-formula-weil). -/
abbrev globalFrobenius (c : WeilCoefficient ell)
    (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ c) :=
  (GlobalGeometricFrobenius.globalGeometricFrobenius D ell hEll X₀ c c₀ K).2

/-- Iterated Frobenius still covers the same iterated base automorphism.
Source: clause (2), compact-support pullback along g_X^m
(blueprint: det-thm-tf-uniform-formula-weil).
Proof: the two projections in the geometric Frobenius definition give the square for
m = 1. Inductively compose that square with itself; associativity gives the m-th square.
For m = 0 both maps are identities. -/
theorem global_return_square (m : ℕ) :
    (End.of (D.geometricFrobenius X₀).hom ^ m) ≫ (D.geometricFiber X₀).hom =
      (D.geometricFiber X₀).hom ≫
        (End.of (GeometricFrobeniusTransport.baseAutomorphism D).hom ^ m) := by
  sorry

/-- The direct m-fold compact-support operator, using normalized exchange along g_X^m
before applying theta^[m]. It is defined independently of powers of the one-step operator.
Source: clause (2), the operator induced by the m-th iterate
(blueprint: det-thm-tf-uniform-formula-weil). -/
def directIterate (c : WeilCoefficient ell)
    (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ c) (m : ℕ) :
    End (compactComplex D ell hEll X₀ c c₀ K) := by
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  letI : QuasiCompact (D.geometricFiber X₀).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let Λ := WeilCoefficient.ab.{u} c
  let a := (D.geometricFiber X₀).hom
  let g := End.of (D.geometricFrobenius X₀).hom
  let b := End.of (GeometricFrobeniusTransport.baseAutomorphism D).hom
  let θ := (leftDerivedUpperStarIsoMapDerivedCategory Λ g).app K.obj.carrier ≪≫ K.obj.str
  letI : IsIso (g ^ m) := (isUnit_iff_isIso (g ^ m)).mp
    (((isUnit_iff_isIso g).mpr inferInstance).pow m)
  letI : IsIso (b ^ m) := (isUnit_iff_isIso (b ^ m)).mp
    (((isUnit_iff_isIso b).mpr inferInstance).pow m)
  let θm := iterate Λ g θ m
  let hM := (boundedConstructible (condensedRingObj Λ (D.geometricFiber X₀).left)).prop_of_iso
    θm.symm K.property
  exact (GeometricFrobeniusTransport.pointInsertion Λ (b ^ m)).hom.app
      ((CohomologyTransport.C Λ c₀).obj K.obj.carrier) ≫
    (GeometricFrobeniusTransport.pointSections Λ (Spec (.of D.k))).map
      (CohomologyTransport.compact Λ (GeometricFrobeniusTransport.compactData D ell hEll c)
          a a (b ^ m) (g ^ m) (global_return_square D X₀ m) c₀ c₀
          ⟨K.obj.carrier, K.property⟩ hM ≫
        (CohomologyTransport.C Λ c₀).map θm.hom)

/-- The direct m-fold Weil operator induces F^m on every compact cohomology group.
Source: clause (2), the separate iterate assertion
(blueprint: det-thm-tf-uniform-formula-weil).
Proof: compute in a compactification descended from X₀, then use the canonical
compactification comparison. Write P_r = L(g_X^r)^*, H = RΓ_c, and t_r for direct
transport. Composition gives t_(m+1) = H(c_m) t_(1,P_m K) t_m. The defining recurrence
of theta^[m] and naturality of t_1 cancel c_m and give U_(m+1) = U_1 U_m. Starting
with U_1 = F, induction gives U_m = F^m. Homology preserves compositions and powers. -/
theorem iterate_on_cohomology (c : WeilCoefficient ell)
    (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ c) (m : ℕ) (_hm : 1 ≤ m) (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).map (directIterate D ell hEll X₀ c c₀ K m) =
      (DerivedCategory.homologyFunctor _ i).map
        (globalFrobenius D ell hEll X₀ c c₀ K ^ m) := by
  sorry

/-- Trace in an arbitrary degree, with the actual coefficient-global-section scalars.
Source: clause (2), each cohomological trace
(blueprint: det-thm-tf-uniform-formula-weil). -/
def cohomologyTrace {ell : ℕ} [Fact ell.Prime] (c : WeilCoefficient ell)
    (C : DerivedCategory (ModuleCat.{u + 1} (scalars.{u} ell c))) (f : End C) (i : ℤ) :=
  LinearMap.trace (scalars.{u} ell c)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (scalars.{u} ell c)) i).obj C)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (scalars.{u} ell c)) i).map f).hom

/-- Finiteness and the cohomological Grothendieck–Lefschetz identity for each positive m.
The finite set bounds compact and all extension-point stalk cohomology, so its sums
are exactly the sums over all integer degrees. Its parity is the integer parity.
Source: clauses (1)--(2)
(blueprint: det-thm-tf-uniform-formula-weil).
Proof: identify the two geometric-Frobenius pair conventions and use Dctf = Dbc for
rational coefficients. The uniform trace formula gives perfectness of the compact
complex and each stalk. Over a field, perfect complexes have finite-dimensional
cohomology supported on finitely many degrees. There are finitely many extension
points, so take the union of their degree supports and the compact degree support.
Identify the uniform formula's global and local operators with the specified returns
and apply the categorical/cohomological trace formula for perfect field complexes.
Adding zero terms outside the degree supports gives the stated common finite sum. -/
theorem formula (c : WeilCoefficient ell)
    (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ c) (m : ℕ) (hm : 1 ≤ m) :
    Finite (D.extensionPoints X₀ m hm) ∧
    (∀ i : ℤ, Module.Finite (scalars ell c) (compactCohomology D ell hEll X₀ c c₀ K i)) ∧
    (∀ (y : D.extensionPoints X₀ m hm) (i : ℤ),
      Module.Finite (scalars ell c) (stalkCohomology D ell hEll X₀ c K m hm y i)) ∧
    ∃ s : Finset ℤ,
      (∀ i : ℤ, i ∉ s → IsZero (compactCohomology D ell hEll X₀ c c₀ K i)) ∧
      (∀ (y : D.extensionPoints X₀ m hm) (i : ℤ), i ∉ s →
        IsZero (stalkCohomology D ell hEll X₀ c K m hm y i)) ∧
      (∑ i ∈ s, (i.negOnePow : ℤ) • cohomologyTrace c
        (compactComplex D ell hEll X₀ c c₀ K) (globalFrobenius D ell hEll X₀ c c₀ K ^ m) i) =
      ∑ᶠ y : D.extensionPoints X₀ m hm,
        ∑ j ∈ s, (j.negOnePow : ℤ) • cohomologyTrace c
          (stalkComplex D ell hEll X₀ c K m hm y)
          (localFrobenius D ell hEll X₀ c K m hm y) j := by
  sorry

/-- The inclusion of a finite coefficient field into Qbar on actual constant scalars.
Source: clause (3), E' → Qbar (blueprint: det-thm-tf-uniform-formula-weil). -/
def scalarInclusion (E : PadicAlgCl.FiniteIntermediateField ell) :
    scalars.{u} ell (.finite E) →+* scalars.{u} ell .qbar :=
  MonObj.Γ.map (weilCoefficientToQbar E)

/-- Every strict Qbar Weil pair has a finite model, including its isomorphism and inverse.
Source: clause (3) and the descent paragraph cited there
(blueprint: det-thm-tf-uniform-formula-weil).
Proof: descend the bounded constructible object to a finite field. The flat pullback
comparison and the filtered Hom-colimit descend theta and its inverse to a common
finite extension. Injectivity in that colimit makes their two inverse equations hold
at a further finite stage, giving a strict Weil pair and the asserted pair isomorphism. -/
theorem finite_model (K : strictWeilComplexCategory D ell hEll X₀ .qbar) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField ell)
      (K' : strictWeilComplexCategory D ell hEll X₀ (.finite E)),
      Nonempty ((weilStrictExtendToQbar D ell hEll X₀ E).obj K'.obj ≅ K.obj) := by
  sorry

/-- For every finite strict model the cohomology tensor comparisons intertwine all
specified powers and returns, and every individual trace extends along E' → Qbar.
Source: clause (3) (blueprint: det-thm-tf-uniform-formula-weil).
Proof: use the flat scalar-six comparisons for compact support, geometric pullback,
and exact point sections. Their tensor/evaluation/counit normalizations intertwine
the direct semilinear transport and the Weil isomorphism. Flatness commutes with
cohomology, giving the displayed tensor-product isomorphisms. Transport further by
the given strict-pair isomorphism. In finite bases scalar extension applies the field
inclusion to each matrix entry, so it carries each trace to its indicated image.
All resulting traces are traces of the fixed operators on K, independent of the model. -/
theorem finite_model_comparison
    (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ .qbar)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (K' : strictWeilComplexCategory D ell hEll X₀ (.finite E))
    (_e : (weilStrictExtendToQbar D ell hEll X₀ E).obj K'.obj ≅ K.obj) :
    (∀ i : ℤ, ∃ e :
      (ModuleCat.extendScalars (scalarInclusion.{u} ell E)).obj
          (compactCohomology D ell hEll X₀ (.finite E) c₀ K' i) ≅
        compactCohomology D ell hEll X₀ .qbar c₀ K i,
      ∀ m : ℕ,
        (ModuleCat.extendScalars (scalarInclusion.{u} ell E)).map
            ((DerivedCategory.homologyFunctor _ i).map
              (globalFrobenius D ell hEll X₀ (.finite E) c₀ K' ^ m)) ≫ e.hom =
          e.hom ≫ (DerivedCategory.homologyFunctor _ i).map
            (globalFrobenius D ell hEll X₀ .qbar c₀ K ^ m)) ∧
    (∀ (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) (j : ℤ), ∃ e :
      (ModuleCat.extendScalars (scalarInclusion.{u} ell E)).obj
          (stalkCohomology D ell hEll X₀ (.finite E) K' m hm y j) ≅
        stalkCohomology D ell hEll X₀ .qbar K m hm y j,
      (ModuleCat.extendScalars (scalarInclusion.{u} ell E)).map
          ((DerivedCategory.homologyFunctor _ j).map
            (localFrobenius D ell hEll X₀ (.finite E) K' m hm y)) ≫ e.hom =
        e.hom ≫ (DerivedCategory.homologyFunctor _ j).map
          (localFrobenius D ell hEll X₀ .qbar K m hm y)) ∧
    (∀ (m : ℕ) (_hm : 1 ≤ m) (i : ℤ),
      scalarInclusion ell E (cohomologyTrace (.finite E)
        (compactComplex D ell hEll X₀ (.finite E) c₀ K')
        (globalFrobenius D ell hEll X₀ (.finite E) c₀ K' ^ m) i) =
      cohomologyTrace .qbar (compactComplex D ell hEll X₀ .qbar c₀ K)
        (globalFrobenius D ell hEll X₀ .qbar c₀ K ^ m) i) ∧
    (∀ (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) (j : ℤ),
      scalarInclusion ell E (cohomologyTrace (.finite E)
        (stalkComplex D ell hEll X₀ (.finite E) K' m hm y)
        (localFrobenius D ell hEll X₀ (.finite E) K' m hm y) j) =
      cohomologyTrace .qbar (stalkComplex D ell hEll X₀ .qbar K m hm y)
        (localFrobenius D ell hEll X₀ .qbar K m hm y) j) := by
  sorry

end WeilConjectures.WeilUniformTrace
