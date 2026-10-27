module

public import Sheaf.CategoryTheory.DgPrincipalHomModels
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Module.LocalizedModule.Exact
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.Algebra.Homology.FiniteStripAugmentation
import Sheaf.CategoryTheory.DgHomotopyAcyclicLocalization

/-! # Finite principal-cover descent for derived dg Hom

Source: Stacks Project, perfect.tex, Tag 08D2, with the dg-Hom refinement and
explicit signs in the DAG proof (blueprint: lem-sfb-dg-finite-principal-hom-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SheafDg.PrincipalHom

variable {S : Type u} [CommRing S] [HasDerivedCategory.{u + 1} (ModuleCat.{u} S)]

/-- Derived pairs and their canonical presentation by actual dg modules.
Source: Stacks, 09KY (blueprint: lem-sfb-dg-finite-principal-hom-descent). -/
abbrev derivedPairs (A : Algebra S) := (moduleQ A).op.prod (moduleQ A)

/-- The actual dg module representing a word-localization object.
Source: Stacks, 0FT5 (blueprint: lem-sfb-dg-finite-principal-hom-descent). -/
def representative {A : Algebra S} (M : Derived A) : LeftModule A :=
  ((Localization.Construction.objEquiv (quasiIsomorphisms A)).symm M).as

/-- Derived dg Hom, computed on every homotopically projective source, naturally
in both chain-map variables. Resolutions are actual quasi-isomorphisms to the
specified representative of every derived object. The additive localization
structure and all cohomology groups are part of the conclusion, not hypotheses.
Source: Stacks, 09KP, 09KM, 09KY, left convention
(blueprint: lem-sfb-dg-finite-principal-hom-descent). -/
structure DerivedHomModel (A : Algebra S) (H : HomModel A) where
  [preadditive : Preadditive (Derived A)]
  quotient_additive : (moduleQ A).Additive
  functor : (Derived A)ᵒᵖ × Derived A ⥤ DerivedCategory (ModuleCat.{u} S)
  resolution (M : Derived A) : LeftModule A
  resolutionMap (M : Derived A) : resolution M ⟶ representative M
  resolution_quasiIso (M : Derived A) : QuasiIso (underlyingMap (resolutionMap M))
  resolution_projective (M : Derived A) : IsHomotopicallyProjective H (resolution M)
  compute (P : LeftModule A) (hP : IsHomotopicallyProjective H P) (N : LeftModule A) :
    DerivedCategory.Q.obj (H.functor.obj (op P, N)) ≅
      functor.obj ((derivedPairs A).obj (op P, N))
  compute_natural {P P' N N' : LeftModule A}
      (hP : IsHomotopicallyProjective H P) (hP' : IsHomotopicallyProjective H P')
      (a : P' ⟶ P) (b : N ⟶ N') :
    DerivedCategory.Q.map (H.functor.map (a.op, b)) ≫ (compute P' hP' N').hom =
      (compute P hP N).hom ≫ functor.map ((derivedPairs A).map (a.op, b))
  cohomology (M N : Derived A) (q : ℤ) :
    Nonempty (((DerivedCategory.homologyFunctor (ModuleCat.{u} S) q).obj
      (functor.obj (op M, N))) ≃+ (M ⟶ (derivedShift A q).obj N))

/-- The canonical independence of resolutions is normalized on every homogeneous
cochain, rather than just asserting existence of unrelated isomorphisms.
Source: Stacks, 09KY (blueprint: lem-sfb-dg-finite-principal-hom-descent). -/
def IsCanonicalHomComparison {A : Algebra S} {H H' : HomModel A}
    (R : DerivedHomModel A H) (R' : DerivedHomModel A H')
    (e : R.functor ≅ R'.functor) : Prop :=
  ∃ c : H.functor ≅ H'.functor,
    (∀ (P N : LeftModule A) (q : ℤ) (z : (H.functor.obj (op P, N)).X q),
      H'.coordinate P N q ((c.hom.app (op P, N)).f q z) = H.coordinate P N q z) ∧
    ∀ (P N : LeftModule A) (hP : IsHomotopicallyProjective H P)
      (hP' : IsHomotopicallyProjective H' P),
      (R.compute P hP N).hom ≫ e.hom.app ((derivedPairs A).obj (op P, N)) =
        DerivedCategory.Q.map (c.hom.app (op P, N)) ≫ (R'.compute P hP' N).hom

/-- Strict finite totals, their derived bifunctor, and the normalized augmentation.
The local derived Hom models are computed on the same localized resolution, so
this is a coherent total of the local derived diagram, not a choice of a total
from separate objects of a triangulated category.
Source: Stacks, 08D2, dg refinement (blueprint: lem-sfb-dg-finite-principal-hom-descent). -/
structure DescentData (A : Algebra S) (r : ℕ) (f : Fin r → S) where
  hom : HomModel A
  derivedHom : DerivedHomModel A hom
  localDiagram : LocalDiagram A hom r f
  localDerivedHom (J : Intersections r) :
    DerivedHomModel (localDiagram.localization J).algebra (localDiagram.hom J)
  localized_projective (J : Intersections r) (P : LeftModule A)
      (hP : IsHomotopicallyProjective hom P) :
    IsHomotopicallyProjective (localDiagram.hom J)
      ((extension (localDiagram.localization J).map).obj P)
  cech : CechModel localDiagram
  total : (Derived A)ᵒᵖ × Derived A ⥤ DerivedCategory (ModuleCat.{u} S)
  compute (P : LeftModule A) (hP : IsHomotopicallyProjective hom P) (N : LeftModule A) :
    DerivedCategory.Q.obj ((cech.diagram.obj (op P, N)).total (.up ℤ)) ≅
      total.obj ((derivedPairs A).obj (op P, N))
  compute_natural {P P' N N' : LeftModule A}
      (hP : IsHomotopicallyProjective hom P) (hP' : IsHomotopicallyProjective hom P')
      (a : P' ⟶ P) (b : N ⟶ N') :
    DerivedCategory.Q.map ((HomologicalComplex₂.totalFunctor
      (ModuleCat.{u} S) (.up ℤ) (.up ℤ) (.up ℤ)).map
        (cech.diagram.map (a.op, b))) ≫ (compute P' hP' N').hom =
      (compute P hP N).hom ≫ total.map ((derivedPairs A).map (a.op, b))
  comparison : derivedHom.functor ⟶ total
  comparison_formula (P : LeftModule A) (hP : IsHomotopicallyProjective hom P)
      (N : LeftModule A) :
    (derivedHom.compute P hP N).hom ≫ comparison.app ((derivedPairs A).obj (op P, N)) =
      DerivedCategory.Q.map (cech.augmentation.app (op P, N)) ≫ (compute P hP N).hom

/-- Derived dg Hom has canonical resolution-independent construction and finite
principal-cover descent, without compactness, boundedness, flatness or Noetherianity.
The comparison is an isomorphism in D(S), natural in both derived variables;
its strict coordinates and total signs are fixed by `DescentData` and `CechModel`.
Source: Stacks, 08D2, refined by 09KP, 09KM and 09KY
(blueprint: lem-sfb-dg-finite-principal-hom-descent).

Proof:
1. Convert left modules to right modules over the graded opposite: a*b=(-1)^(ab)ba,
   x*a=(-1)^(xa)ax. Apply lem-sfb-dg-property-p-resolution and
   lem-sfb-dg-property-p-homotopically-projective. Translate back; the central
   degree-zero S-action makes all Hom maps and homotopies S-linear.
2. Apply lem-sfb-dg-homotopically-projective-hom-derived also to shifts. Cycles
   of degree q are maps to N[q], and boundaries are homotopies. Lift comparisons
   between projective resolutions; inverse lifts compose to identities up to
   homotopy. Precomposition gives the unique normalized derived Hom comparison.
3. By lem-weil-pbc-localization-module-exact, localization commutes with cycles,
   boundaries and cohomology. Extension is ordinary localization, using
   (c/s) tensor x ↦ cx/s and x/s ↦ (1/s) tensor x. Apply the action-normalized
   adjunction lem-sfb-ringed-dg-scalar-adjunction and descend its exact functors.
4. Restriction h ↦ (x ↦ h(x/1)) identifies Hom(P_f,L) with Hom(P,Res L).
   Its inverse is h ↦ (x/s ↦ h(x)/s); it respects the Hom differential and all
   further localizations. Thus P_f is homotopically projective whenever P is.
5. Form B^(p,t)=product over |J|=p+1 of (N_fJ)^t. The finite total has
   differential delta+(-1)^p d_N and column-p left action (-1)^(p|c|)c.
   Direct sign calculation gives the Leibniz identity. The singleton maps
   give a dg augmentation u:N→T(N), with zero higher components.
6. Apply lem-pc-affine-cech-complex in every integer degree and then
   lem-sc-finite-strip-row-augmentation. The horizontal augmented rows are
   exact and the width r is finite, even for unbounded N. Hence u is a quasi-iso.
7. By lem-sfb-dg-homotopy-acyclic-localization, Cone(u) is acyclic. Homotopical
   projectivity makes Hom(P,Cone(u)) acyclic. Its component differential is
   (da+ub,-db), so it is Cone(Hom(P,u)); consequently Hom(P,u) is a quasi-iso.
8. A degree-q map into T(N) has components of degree q-p in N_fJ. Finite
   regrouping commutes with the product over all source degrees, without a
   bound on P. The Hom differential becomes delta+(-1)^p d_Hom exactly.
9. Apply step 4 simultaneously on all intersections. The resulting strict
   diagram gives the specified derived total and comparison. Its singleton
   component is h ↦ (x/s ↦ h(x)/s). All formulas commute with maps; homotopic
   resolution lifts give homotopic comparisons. This gives naturality and
   canonical independence. For r=1 the generator is a unit; zero localizations
   and zero modules contribute zero coordinates. No other hypothesis was used. -/
theorem finite_principal_hom_descent (A : Algebra S) (r : ℕ) (hr : 1 ≤ r)
    (f : Fin r → S) (hf : Ideal.span (Set.range f) = ⊤) :
    (∀ g : S, Nonempty (LocalizationModel A g)) ∧
    ∃ d : DescentData A r f,
      (∀ Z : (Derived A)ᵒᵖ × Derived A, IsIso (d.comparison.app Z)) ∧
      ∀ (H' : HomModel A) (R' : DerivedHomModel A H'),
        ∃! e : d.derivedHom.functor ≅ R'.functor,
          IsCanonicalHomComparison d.derivedHom R' e := by
  sorry

end CategoryTheory.SheafDg.PrincipalHom
