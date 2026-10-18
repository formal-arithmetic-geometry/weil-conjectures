module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# A finitary étale site for a quasi-compact quasi-separated scheme

Source: Stacks Project, `topologies.tex`, Tags 021D and 04HR (blueprint:
lem-trf-qcqs-etale-finitary-site).
-/


@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u v w

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The separated, finite-presentation objects of the small étale site.
Source: Stacks Project, `topologies.tex`, Tags 021D and 04HR
(blueprint: lem-trf-qcqs-etale-finitary-site). -/
def etaleFinitaryProperty (T : Scheme.{u}) : ObjectProperty T.Etale :=
  fun A => IsSeparated A.hom ∧ LocallyOfFinitePresentation A.hom ∧
    QuasiCompact A.hom ∧ QuasiSeparated A.hom

/-- The full finitary étale subcategory of `T.Etale`.
Source: Stacks Project, `topologies.tex`, Tags 021D and 04HR
(blueprint: lem-trf-qcqs-etale-finitary-site). -/
abbrev EtaleFinitary (T : Scheme.{u}) :=
  (etaleFinitaryProperty T).FullSubcategory

/-- Finite jointly-surjective families in `EtaleFinitary T`.
Source: Stacks Project, Sites, Definition 00VH and `topologies.tex`, Tags 021D and 04HR
(blueprint: lem-trf-qcqs-etale-finitary-site). -/
def finiteJointlySurjectivePrecoverage (T : Scheme.{u}) :
    Precoverage (EtaleFinitary T) where
  coverings X := {R |
    R.uncurry.Finite ∧
      ∀ x : X.obj.left, ∃ (Y : EtaleFinitary T) (f : Y ⟶ X),
        R f ∧ x ∈ Set.range f.hom.left.base}

/-- The generated topology of finite jointly-surjective families.
Source: Stacks Project, Sites, Definition 00VH and `topologies.tex`, Tags 021D and 04HR
(blueprint: lem-trf-qcqs-etale-finitary-site). -/
def finiteJointlySurjectiveTopology (T : Scheme.{u}) :
    GrothendieckTopology (EtaleFinitary T) :=
  (finiteJointlySurjectivePrecoverage T).toGrothendieck

/-- The finitary étale site for a qcqs scheme.
Source: Stacks Project, `topologies.tex`, Tags 021D and 04HR
(blueprint: lem-trf-qcqs-etale-finitary-site).

The clauses are, in order: the identity object `T → T` is a terminal object; finite limits
exist and are computed in `T.Etale`; every object is a qcqs scheme; finite jointly
surjective families form a site; their topology is the topology induced from the small
étale site; restriction `ι.sheafPushforwardContinuous` is an equivalence on sheaves of sets
(in `Type u`); and for every `e : T' ⟶ T` between qcqs schemes, scheme base change
restricts to a finite-limit-preserving, cover-preserving functor.

Proof (node lem-trf-qcqs-etale-finitary-site, steps 1-7).
1. `T → T` is étale, separated and of finite presentation and terminal. Each object is
   qcqs (lem-weil-pbc-qcqs-morphism-permanence (2)); a `T`-map between objects is étale,
   separated and of finite presentation (lem-weil-pbc-etale-composition-cancellation,
   lem-weil-pbc-separated-cancellation, lem-weil-pbc-qcqs-morphism-permanence (1)).
2. For `A → C ← B` the fibre product `A ×_C B` is separated and of finite presentation over
   `T` (lem-weil-pbc-separated-base-change, lem-weil-pbc-qcqs-morphism-permanence (3),
   lem-weil-pbc-proper-fp-permanence (d),(e)) and is the étale-site fibre product
   (lem-weil-pbc-etale-base-change-finite-limits); terminal object and pullbacks give all
   finite limits, preserved by the inclusion (lem-weil-pbc-finite-limits-from-terminal-pullbacks).
3. Affine opens of an étale `U → T` lie in the subcategory (lem-weil-pbc-affine-source-
   morphism-separated, lem-weil-pbc-qcqs-morphism-permanence (1)); a full-site cover of an
   object is refined by finitely many of them (lem-weil-pbc-etale-morphism-open-map,
   quasi-compactness); the empty object takes the empty family.
4. Finite jointly surjective families satisfy the site axioms
   (lem-weil-pbc-etale-covering-composition, lem-weil-pbc-etale-covering-base-change,
   step 2); their covering sieves are those containing such a family
   (lem-weil-pbc-pretopology-sheaf-condition).
5. A sieve is covering iff the full-site sieve it generates is covering (steps 3, 4 and
   def-weil-pbc-etale-site); this is the topology induced from the small étale site.
6. The dense-subsite comparison lem-pc-fppf-dense-sheaf-equivalence makes restriction an
   equivalence of sheaves of sets.
7. Base change along any `e` (lem-weil-pbc-etale-base-change-finite-limits,
   lem-weil-pbc-separated-base-change, lem-weil-pbc-qcqs-morphism-permanence (3)) preserves
   the subcategory and its finite limits (step 2), and finite covering families
   (lem-weil-pbc-etale-covering-base-change); no hypothesis on `e` is used.
-/
theorem exists_qcqs_etale_finitary_site (T : Scheme.{u}) [CompactSpace T]
    [QuasiSeparatedSpace T] :
    (∃ A : EtaleFinitary T,
      A.obj = Etale.mk (𝟙 T) ∧ Nonempty (IsTerminal A)) ∧
    HasFiniteLimits (EtaleFinitary T) ∧
    PreservesFiniteLimits (etaleFinitaryProperty T).ι ∧
    (∀ A : EtaleFinitary T,
      CompactSpace A.obj.left ∧ QuasiSeparatedSpace A.obj.left) ∧
    (finiteJointlySurjectivePrecoverage T).IsSiteForCoverings ∧
    finiteJointlySurjectiveTopology T =
      (etaleFinitaryProperty T).ι.inducedTopology T.smallEtaleTopology ∧
    (∃ _ : (etaleFinitaryProperty T).ι.IsContinuous (finiteJointlySurjectiveTopology T)
        T.smallEtaleTopology,
      ((etaleFinitaryProperty T).ι.sheafPushforwardContinuous (Type u)
        (finiteJointlySurjectiveTopology T) T.smallEtaleTopology).IsEquivalence) ∧
    (∀ (T' : Scheme.{u}) [CompactSpace T'] [QuasiSeparatedSpace T']
      (e : T' ⟶ T), ∃ F : EtaleFinitary T ⥤ EtaleFinitary T',
        PreservesFiniteLimits F ∧
        Nonempty (F ⋙ (etaleFinitaryProperty T').ι ≅
          (etaleFinitaryProperty T).ι ⋙
            MorphismProperty.Over.pullback @Etale (⊤ : MorphismProperty Scheme) e) ∧
        (∀ {X : EtaleFinitary T} {R : Sieve X},
          R ∈ finiteJointlySurjectiveTopology T X →
            Sieve.functorPushforward F R ∈
              finiteJointlySurjectiveTopology T' (F.obj X))) := by
  sorry

end AlgebraicGeometry.Scheme
