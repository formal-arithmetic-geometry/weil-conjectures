module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Topology.LocallyConstant.Algebra

/-! # Finite abelian bundles on a profinite slice

Source: the finite-bundle definition in lem-sfb-relative-finite-bundle-roos, motivated by
Ruimy--Tubach--Wolf, Lemma 1.2.7 (blueprint: def-sfb-relative-finite-bundle-model).
A locally constant finite partition records disjoint clopen pieces, including empty pieces.
The sections are continuous maps to the finite discrete groups on each pulled-back piece.
-/

@[expose] public section

set_option autoImplicit false

universe u v r s

open CategoryTheory Opposite

namespace Profinite

/-- The actual coefficient sheaf on the profinite slice, obtained by restriction of C(-,T).
Source: lem-sfb-relative-finite-bundle-roos, opening coefficient formula
(blueprint: def-sfb-relative-finite-bundle-model). -/
noncomputable abbrev relativeContinuousRing (P : Profinite.{u}) (T : Type v)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    Sheaf ((coherentTopology Profinite.{u}).over P) RingCat.{max u v + 1} :=
  (continuousMapRingSheafOfUniverse.{u, v} T).over P

/-- A finite locally constant abelian bundle is the disjoint union, over a finite clopen
partition of P, of a piece times a finite discrete abelian group.
Source: lem-sfb-relative-finite-bundle-roos, finite-bundle definition
(blueprint: def-sfb-relative-finite-bundle-model). -/
structure FiniteAbelianBundle (P : Profinite.{u}) where
  n : ℕ
  partition : LocallyConstant P (Fin n)
  group : Fin n → AddCommGrpCat.{u}
  finite : ∀ i : Fin n, Finite (group i)

namespace FiniteAbelianBundle

/-- Continuous sections after pullback to Q: finite discrete targets make continuous maps
exactly locally constant maps. Source: lem-sfb-relative-finite-bundle-roos, bundle hypothesis
(blueprint: def-sfb-relative-finite-bundle-model). -/
abbrev sections {P : Profinite.{u}} (E : FiniteAbelianBundle P) (Q : Over P) : Type u :=
  ∀ i : Fin E.n, LocallyConstant {q : Q.left // E.partition (Q.hom q) = i} (E.group i)

/-- Restriction of bundle sections is precomposition with the actual map of test spaces.
Source: lem-sfb-relative-finite-bundle-roos, sheaf of continuous sections
(blueprint: def-sfb-relative-finite-bundle-model). -/
def restrict {P : Profinite.{u}} (E : FiniteAbelianBundle P)
    {Q Q' : Over P} (f : Q ⟶ Q') (s : E.sections Q') : E.sections Q :=
  fun i ↦ LocallyConstant.comap
    ⟨fun q ↦ ⟨f.left q.val, by
        have h := ConcreteCategory.congr_hom (Over.w f) q.val
        change Q'.hom (f.left q.val) = Q.hom q.val at h
        exact (congrArg E.partition h).trans q.property⟩,
      (f.left.hom.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩ (s i)

/-- An additive, restriction-compatible presentation of the underlying sheaf as continuous
sections of the specified finite bundle. It imposes no condition on the scalar action.
Every map between such sheaves is a continuous fibrewise additive bundle map by Yoneda:
the total bundle is a profinite object over P and its section presheaf is representable.
Source: lem-sfb-relative-finite-bundle-roos, finite-bundle and transition hypotheses
(blueprint: def-sfb-relative-finite-bundle-model). -/
structure SectionPresentation {P : Profinite.{u}} (E : FiniteAbelianBundle P)
    {R : Sheaf ((coherentTopology Profinite.{u}).over P) RingCat.{r}}
    (M : SheafOfModules.{s} R) where
  equiv : ∀ Q : Over P, M.val.obj (op Q) ≃+ E.sections Q
  naturality : ∀ (Q Q' : Over P) (f : Q ⟶ Q') (x : M.val.obj (op Q')),
    equiv Q (M.val.map f.op x) = E.restrict f (equiv Q' x)

end FiniteAbelianBundle
end Profinite
