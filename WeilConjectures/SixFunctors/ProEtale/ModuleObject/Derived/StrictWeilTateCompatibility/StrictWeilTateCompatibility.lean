/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedDerivedTensorComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportGeometry
public import WeilConjectures.CategoryTheory.Endofunctor.StrictPairTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilTateFiniteness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilTateScalarLine

/-! # Tate twists and finite scalar extension for condensed strict Weil complexes

Source: latest blueprint, part-weights-riemann-hypothesis/sec-weights-deligne-theorem/
sec-wdef-weights/sk-r-real-linear/lem-wf-tate-twist-compatibility.md,
Compatibility of the Tate twists (blueprint: lem-wf-tate-twist-compatibility).

All carriers lie in the ordinary derived category of internal modules over the
pulled-back condensed coefficient ring. The root-normalized signed Tate line,
its Frobenius arrow, and the exact derived action are the published constructions.
The functor formulas below determine the twist on every object and morphism;
the last clause gives its compatibility with finite scalar extension.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilTateCompatibility

open PurityTransport StrictWeilCondensed

variable (ell : ℕ) [Fact ell.Prime]

/-- The ambient fixed-pair category for the recorded exact derived action.
Source: latest blueprint, ordinary derived categories and strict pairs
(blueprint: lem-wf-tate-twist-compatibility). -/
abbrev Ambient (c : Coefficient ell) {X : Scheme.{u}} (g : X ≅ X) :=
  CategoryTheory.Endofunctor.IsoAlgebra (action (c.obj ell) g)

/-- The existing bounded constructible finite-Tor condition on an ambient carrier.
Source: latest blueprint, final restriction clause
(blueprint: lem-wf-tate-twist-compatibility). -/
def Small (c : Coefficient ell) (X : Scheme.{u}) : ObjectProperty (c.derived ell X) :=
  constantModelBoundedConstructible (c.obj ell) X ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K

/-- The canonical composition comparison P_F B to B P_E. It is obtained by
left deriving the ordinary balanced pullback/scalar comparison, then using the
canonical identification of exact derived pullback with termwise pullback.
Source: latest blueprint, c and the coefficient square
(blueprint: lem-wf-tate-twist-compatibility). -/
def scalarFrobenius {X : Scheme.{u}} (g : X ≅ X)
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
    finiteCoefficientDerivedExtension X ell h ⋙ action ((Coefficient.rational F).obj ell) g ≅
      action ((Coefficient.rational E).obj ell) g ⋙
        finiteCoefficientDerivedExtension X ell h :=
  tateScalarComparison ell g h

/-- Finite scalar extension on strict pairs. The existing fixed-pair transport
sends (K, phi) to (BK, c_K followed by B(phi)) and h to B(h).
Source: latest blueprint, B on strict pairs
(blueprint: lem-wf-tate-twist-compatibility). -/
def scalarExtension {X : Scheme.{u}} (g : X ≅ X)
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
    Ambient ell (.rational E) g ⥤ Ambient ell (.rational F) g :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso (scalarFrobenius ell g h)

/-- The full displayed twist formula, including its action on morphisms and its
restriction to the recorded Dctf. HEq only accommodates the carrier equality in
an existentially quantified functor; the prescribed maps themselves are fixed.
Source: latest blueprint, (K, phi)(m) and h(m)
(blueprint: lem-wf-tate-twist-compatibility). -/
def TwistFormula {X : Scheme.{u}} (g : X ≅ X)
    [∀ x : X, Invertible (ell : X.residueField x)] (c : Coefficient ell) (m : ℤ)
    (T : Ambient ell c g ⥤ Ambient ell c g) : Prop :=
  (∀ K : Ambient ell c g,
    (T.obj K).carrier = K.carrier ⊗ derivedTateLine ell c X m ∧
    HEq (T.obj K).str
      (tensorDatum (c.obj ell) g K.str (tateDatum ell c g m))) ∧
  (∀ (K L : Ambient ell c g) (h : K ⟶ L),
    HEq (T.map h).hom.f (h.hom.f ⊗ₘ 𝟙 (derivedTateLine ell c X m))) ∧
  (∀ K : Ambient ell c g,
    Small ell c X K.carrier → Small ell c X (T.obj K).carrier)

/-- The ambient tensor functor, constructed without any geometric finiteness assertion. -/
private def twistFunctor {X : Scheme.{u}} (g : X ≅ X)
    [∀ x : X, Invertible (ell : X.residueField x)] (c : Coefficient ell) (m : ℤ) :
    Ambient ell c g ⥤ Ambient ell c g :=
  CategoryTheory.Endofunctor.IsoAlgebra.tensorWith
    (action (c.obj ell) g) (tateDatum ell c g m)

/-- The functor formulas and Small preservation are independent of scalar comparison. -/
private theorem twistFormula_tensor {X : Scheme.{u}} (g : X ≅ X)
    [∀ x : X, Invertible (ell : X.residueField x)] (c : Coefficient ell) (m : ℤ) :
    TwistFormula ell g c m (twistFunctor ell g c m) := by
  refine ⟨(fun K ↦ ⟨rfl, ?_⟩), (fun K L h ↦ HEq.rfl), ?_⟩
  · apply heq_of_eq
    exact CategoryTheory.Endofunctor.IsoAlgebra.tensorRight_obj_str _ _ K
  · intro K hK
    exact (tate_finiteness ell X).1 c m K.carrier hK

/-- The equivariant scalar line lifts through the proved categorical tensor comparison. -/
private theorem twist_scalar {X : Scheme.{u}} (g : X ≅ X)
    [∀ x : X, Invertible (ell : X.residueField x)]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) (m : ℤ) :
    Nonempty (twistFunctor ell g (.rational E) m ⋙ scalarExtension ell g h ≅
      scalarExtension ell g h ⋙ twistFunctor ell g (.rational F) m) := by
  exact CategoryTheory.Endofunctor.IsoAlgebra.tensorRightScalarIso_nonempty
    (finiteCoefficientDerivedExtension X ell h) (scalarFrobenius ell g h)
    (tateDatum ell (.rational E) g m) (tateDatum ell (.rational F) g m)
    (tate_scalar_line ell g h m)

/-- Assemble the formulas, scalar preservation and scalar comparison. -/
private theorem compatibility_of_invertible {X : Scheme.{u}} (g : X ≅ X)
    [∀ x : X, Invertible (ell : X.residueField x)] :
    ∃ T : (c : Coefficient ell) → ℤ → Ambient ell c g ⥤ Ambient ell c g,
      (∀ (c : Coefficient ell) (m : ℤ), TwistFormula ell g c m (T c m)) ∧
      (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F),
        ∀ K : Ambient ell (.rational E) g,
          Small ell (.rational E) X K.carrier →
            Small ell (.rational F) X ((scalarExtension ell g h).obj K).carrier) ∧
      (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F) (m : ℤ),
        Nonempty (T (.rational E) m ⋙ scalarExtension ell g h ≅
          scalarExtension ell g h ⋙ T (.rational F) m)) := by
  refine ⟨twistFunctor ell g, twistFormula_tensor ell g, ?_, ?_⟩
  · intro E F h K hK
    exact (tate_finiteness ell X).2 E F h K.carrier hK
  · intro E F h m
    exact twist_scalar ell g h m

/-- Every signed root-normalized Tate twist is a functor of strict Weil pairs,
and it commutes naturally with every finite intermediate coefficient extension.
The final two clauses restrict the ambient functors and their isomorphisms to Dctf.
The existential invertibility witness is a conclusion, derived from ell != p,
not an additional hypothesis on the geometric fibre or its residue fields.

Source: latest blueprint, Compatibility of the Tate twists, statement and proof
(blueprint: lem-wf-tate-twist-compatibility).

Proof: geometric Frobenius is the semilinear automorphism attached to the fixed
finite-field datum. Since ell differs from p, ell is invertible on its geometric
fibre. Pull back the finite root sheaves functorially; their power transitions
commute with pullback. The automorphism's inverse-image equivalence preserves
inverse limits, scalar inversion and the specified finite-subextension colimit.
This is the normalized tatePull of the published dependency, including the unit,
positive tensor powers and evaluation-compatible negative duals. Its degree-zero
image is tateDatum. Compose the inverse derived tensorator with phi tensor tau_m.
Naturality of that tensorator gives the morphism formula and the functor laws.

For E contained in F, choose the common compatible-root cover. Its root frames
identify F tensor E(1) with F(1), sending a tensor (e x) to e(ax). Rescaling e
rescales both expressions equally, so the maps and their inverses glue. Root
pullback commutes with coefficient inclusion. Tensor powers and evaluation give
the same Frobenius square in all signed degrees. The canonical derived scalar
comparison scalarFrobenius is monoidal, so its tensor comparison followed by
one tensor this signed-line identification is a morphism of strict pairs.
Its inverse and naturality give the asserted natural isomorphism.

Finally signed lines trivialize on that same cover, so their twists preserve
bounded constructibility and each finite Tor interval. Finite field extension
is finite free, hence exact, and extends finite presentation matrices on the
same strata. Tensor association preserves the Tor interval under extension.
Thus both functors preserve Small, and full-subcategory restriction carries
the ambient natural isomorphism to the strict Dctf categories. -/
theorem compatibility (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (X₀ : Over (Spec (.of D.k₀))) :
    ∃ hInv : ∀ x : (pullback X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) : Scheme.{u}),
        Invertible (ell : (pullback X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).residueField x),
      (fun [i : ∀ x : (pullback X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) : Scheme.{u}),
          Invertible (ell : (pullback X₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).residueField x)] ↦
        ∃ T : (c : Coefficient ell) → ℤ →
            Ambient ell c (modelFrobenius D X₀) ⥤ Ambient ell c (modelFrobenius D X₀),
          (∀ (c : Coefficient ell) (m : ℤ),
            TwistFormula ell (modelFrobenius D X₀) c m (T c m)) ∧
          (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F),
            ∀ K : Ambient ell (.rational E) (modelFrobenius D X₀),
              Small ell (.rational E) _ K.carrier →
                Small ell (.rational F) _
                  ((scalarExtension ell (modelFrobenius D X₀) h).obj K).carrier) ∧
          (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F) (m : ℤ),
            Nonempty (T (.rational E) m ⋙ scalarExtension ell (modelFrobenius D X₀) h ≅
              scalarExtension ell (modelFrobenius D X₀) h ⋙ T (.rational F) m)))
        (i := hInv) := by
  let X : Scheme.{u} :=
    pullback X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  let π : X ⟶ Spec (.of D.k) :=
    pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  let hInv : ∀ x : X, Invertible (ell : X.residueField x) := fun x ↦
    (show IsUnit (ell : X.residueField x) by
      simpa only [map_natCast] using
        (primeUnit D ell hEll).map (π.residueFieldAlgebraMap x)).invertible
  refine ⟨hInv, ?_⟩
  let := hInv
  exact compatibility_of_invertible ell (modelFrobenius D X₀)

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilTateCompatibility
