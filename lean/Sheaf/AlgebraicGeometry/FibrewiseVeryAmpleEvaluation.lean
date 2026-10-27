module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange
import WeilConjectures.AlgebraicGeometry.Picard.CanonicalDirectImageH0Unit
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
import Sheaf.AlgebraicGeometry.UniversalClosedImmersionOpen

/-! # Evaluation of a fibrewise very ample line bundle

Source: Stacks Project, Tags 0CTM, 0B91, 0BCD, 08HY, 01OB, 01OD and 05XA
(blueprint: lem-sfb-fibrewise-very-ample-evaluation).

The complete linear system is expressed by its evaluation quotient and the normalized
projective-bundle quotient classification. Over a field, direct image to its spectrum
is the quasi-coherent module of all global sections. Base change below uses the actual
canonical module base-change map, not an unspecified isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

open Scheme.Modules ProjectiveBundleQuotientGeometry

/-- A line bundle with very ample complete linear systems and vanishing first
cohomology on geometric fibres has finite locally free direct image. Its evaluation
is a closed embedding, compatible with arbitrary base change, including the tautological
line and quotient. Finite rank is allowed to vary on the base.

Source: Stacks Project, spaces-perfect.tex Tag 0CTM, perfect.tex Tag 0B91,
more-algebra.tex Tag 0BCD, cohomology.tex Tag 08HY, constructions.tex Tags 01OB and 01OD,
and spaces-more-morphisms.tex Tag 05XA
(blueprint: lem-sfb-fibrewise-very-ample-evaluation).

Proof:
1. L is finitely presented and flat over T, since it is locally the structure sheaf
and f is flat. Apply lem-pc-rf-perfect-base-change to K = Rf_*(L[0]). It is perfect
with canonical arbitrary derived base change. Lem-pc-canonical-direct-image-h0-unit
identifies H0(K) with E = f_*L.
2. At t extend its residue field to an algebraic closure. Faithful exact extension
of vector spaces and the fibre H1 hypothesis give vanishing in degree one; negative
cohomology vanishes as well. Lem-sc-perfect-finite-free-residue-model gives locally
a bounded finite free model P with P^{<0} = P^1 = 0, hence P = P^0[0] plus P^{>=2}.
3. E is locally P^0. Lem-pc-flat-complex-derived-pullback computes every pullback
termwise, retaining this splitting. Both degree-zero comparisons are isomorphisms;
lem-pc-canonical-degree-zero-mate-square identifies their composite with the ordinary
canonical module base-change map. Local inverses agree, proving arbitrary base change.
4. The ordinary counit-mate identity of lem-pc-module-pullback-adjunction identifies
pulled-back evaluation with evaluation after the canonical base-change map. On every
geometric fibre it is therefore the complete-linear-system quotient in the hypothesis.
5. At any point trivialize L. The image ideal of evaluation generates the geometric
residue field, so it cannot lie in the maximal ideal. It contains a unit. Evaluation
is consequently stalkwise surjective, with no reducedness assumption.
6. Lem-trf-projective-bundle-quotient-geometry gives its classifying T-morphism j,
with quotient-compatible j^*O(1) isomorphic to L, into the separated bundle P_T(E).
7. Apply lem-sfb-universal-closed-immersion-open. Properness supplies universal
closedness and local finite type. Every geometric point lies in its universal open
locus, by the fibre hypothesis, so this locus is T. The identity test gives that j
itself is a closed immersion, including over nonreduced bases.
8. For any h the quotient classification identifies P(E') with P(E) times_T T',
where E' is the base-changed direct image and the coefficient identification is the
canonical base-change map of step 3. Its pullback quotient is exactly evaluation by
step 4. Uniqueness identifies the two embeddings and their line identifications.
All arguments are local at individual base points; no finite base cover is required. -/
theorem fibrewise_very_ample_evaluation
    {Y T : Scheme.{u}} (f : Y ⟶ T) [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f] (L : Y.Modules) [L.IsInvertible]
    (hdim : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ T),
      topologicalKrullDim (pullback f a : Scheme.{u}) ≤ (1 : WithBot ℕ∞))
    (hH1 : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ T),
      IsZero ((RingedSpace.moduleCohomology (pullback f a).toRingedSpace 1).obj
        ((tensorPullback (pullback.fst f a)).obj L)))
    (hvery : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ T),
      Epi ((tensorPullbackSectionAdjunction (pullback.snd f a)).counit.app
        ((tensorPullback (pullback.fst f a)).obj L)) ∧
      ∃ hE : ((pushforward (pullback.snd f a)).obj
          ((tensorPullback (pullback.fst f a)).obj L)).IsQuasicoherent,
        ∃ D : @TautologicalQuotient (Spec (.of Ω))
            ((pushforward (pullback.snd f a)).obj
              ((tensorPullback (pullback.fst f a)).obj L)) hE,
          ∃ j : pullback f a ⟶ (@SymmetricAlgebraSheaf.gradedAlgebraData
              (Spec (.of Ω)) ((pushforward (pullback.snd f a)).obj
                ((tensorPullback (pullback.fst f a)).obj L)) hE).relProj,
            IsClosedImmersion j ∧
            Classifies D (pullback.snd f a) ((tensorPullback (pullback.fst f a)).obj L)
              ((tensorPullbackSectionAdjunction (pullback.snd f a)).counit.app
                ((tensorPullback (pullback.fst f a)).obj L)) j) :
    ((pushforward f).obj L).IsFiniteLocallyFree ∧
    (∀ (T' : Scheme.{u}) (h : T' ⟶ T),
      IsIso (moduleBaseChangeMap f (pullback.snd f h) h (pullback.fst f h)
        pullback.condition L)) ∧
    Epi ((tensorPullbackSectionAdjunction f).counit.app L) ∧
    ∃ hE : ((pushforward f).obj L).IsQuasicoherent,
      ∃ D : @TautologicalQuotient T ((pushforward f).obj L) hE,
        ∃ j : Y ⟶ (@SymmetricAlgebraSheaf.gradedAlgebraData
            T ((pushforward f).obj L) hE).relProj,
          IsClosedImmersion j ∧
          Classifies D f L ((tensorPullbackSectionAdjunction f).counit.app L) j ∧
          ∀ (T' : Scheme.{u}) (h : T' ⟶ T),
            Epi ((tensorPullbackSectionAdjunction (pullback.snd f h)).counit.app
              ((tensorPullback (pullback.fst f h)).obj L)) ∧
            ∃ hE' : ((pushforward (pullback.snd f h)).obj
                ((tensorPullback (pullback.fst f h)).obj L)).IsQuasicoherent,
              ∃ D' : @TautologicalQuotient T'
                  ((pushforward (pullback.snd f h)).obj
                    ((tensorPullback (pullback.fst f h)).obj L)) hE',
                ∃ j' : pullback f h ⟶ (@SymmetricAlgebraSheaf.gradedAlgebraData T'
                    ((pushforward (pullback.snd f h)).obj
                      ((tensorPullback (pullback.fst f h)).obj L)) hE').relProj,
                  IsClosedImmersion j' ∧
                  Classifies D' (pullback.snd f h)
                    ((tensorPullback (pullback.fst f h)).obj L)
                    ((tensorPullbackSectionAdjunction (pullback.snd f h)).counit.app
                      ((tensorPullback (pullback.fst f h)).obj L)) j' ∧
                  ∃ r : (@SymmetricAlgebraSheaf.gradedAlgebraData T'
                      ((pushforward (pullback.snd f h)).obj
                        ((tensorPullback (pullback.fst f h)).obj L)) hE').relProj ⟶
                      (@SymmetricAlgebraSheaf.gradedAlgebraData
                        T ((pushforward f).obj L) hE).relProj,
                    IsPullback r
                      (@SymmetricAlgebraSheaf.gradedAlgebraData T'
                        ((pushforward (pullback.snd f h)).obj
                          ((tensorPullback (pullback.fst f h)).obj L)) hE').relProjHom
                      (@SymmetricAlgebraSheaf.gradedAlgebraData
                        T ((pushforward f).obj L) hE).relProjHom h ∧
                    pullback.fst f h ≫ j = j' ≫ r ∧
                    Classifies D
                      ((@SymmetricAlgebraSheaf.gradedAlgebraData T'
                        ((pushforward (pullback.snd f h)).obj
                          ((tensorPullback (pullback.fst f h)).obj L)) hE').relProjHom ≫ h)
                      D'.line
                      ((tensorPullbackSectionComp
                        (@SymmetricAlgebraSheaf.gradedAlgebraData T'
                          ((pushforward (pullback.snd f h)).obj
                            ((tensorPullback (pullback.fst f h)).obj L)) hE').relProjHom
                        h).hom.app ((pushforward f).obj L) ≫
                        (tensorPullback
                          (@SymmetricAlgebraSheaf.gradedAlgebraData T'
                            ((pushforward (pullback.snd f h)).obj
                              ((tensorPullback (pullback.fst f h)).obj L)) hE').relProjHom).map
                          (moduleBaseChangeMap f (pullback.snd f h) h (pullback.fst f h)
                            pullback.condition L) ≫ D'.quotient) r := by
  sorry

end AlgebraicGeometry
