## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAcyclicAffinizationGeometry` states
`AlgebraicGeometry.AlgebraicSpace.space_acyclic_affinization_geometry` with a single
`sorry`. It also defines `acyclicAffinizationAbsoluteSpace` by projecting the
characterized change-of-base functor of `exists_spaceChangeBase`. This is real
functor data selected from its universal characterization, not an arbitrary map
or a choice from uncharacterized existence. No theorem is proved in this delivery.

Hypothesis and clause mapping:

- The arbitrary scheme S is `{S : Scheme.{u}}`; X is `(X : AlgebraicSpace S)`.
- Every open cover has a finite subcover is `CompactSpace (Point X.obj.obj)`.
- Quasi-compactness of the absolute diagonal is `IsAbsolutelyQuasiSeparated X`,
  the existing equivalent affine-pair criterion of Stacks 0AHR. This retains
  arbitrary, possibly non-quasi-separated bases S.
- Modules are exactly `X.Modules` on the recorded small etale ringed site;
  `F.IsQuasicoherent` is Mathlib's recorded local-presentation predicate, with
  the existing algebraic-space slice instances imported.
- H1 vanishing for every such F is `hH`, using `Subsingleton (Sheaf.H
  ((SheafOfModules.toSheaf X.structureSheaf).obj F) 1)`. The underlying additive
  sheaf and global derived sections are the stated cohomology, not a different
  cohomology of module objects. `HasSheafify` and `HasExt` are the same infrastructure
  choices as the already recorded affine-base-change theorem, retaining section
  universe u and cohomology universe u+1; neither is a geometric restriction.
- Absolute X is `acyclicAffinizationAbsoluteSpace X`. Its definition invokes
  the already recorded `exists_spaceChangeBase` at the unique scheme map
  S -> Spec(ULift Z). That theorem characterizes the sigma formula, restriction
  maps, atlas and ringed-site equivalence, including non-separated S.
- A = Gamma(X,O_X) is expressed without inventing a second global-sections
  definition: `A : CommRingCat.{u}` with the cone `pi` (Lean variable `π`) on
  `absoluteX.etaleForget.op ⋙ Scheme.Γ` and `Nonempty (IsLimit (Cone.mk A π))`.
  A compatible family of regular functions on all small etale charts is exactly
  a global section of the structure sheaf. The normalized site equivalence
  identifies these with the global functions of the original X. A limiting
  cone specifies this ring up to its unique compatible ring isomorphism.
- Existence of the absolute morphism is `∃ p : absoluteX ⟶ schemeSpace (...)`.
  The affine target uses its unique structure morphism to Spec(ULift Z).
- Identity on A is the equality for each chart T between `π.app (op T)` and
  `(Scheme.ΓSpecIso A).inv ≫ (yoneda.preimage
  (T.obj.hom ≫ p.hom.hom)).left.appTop`. Thus it is the actual pullback of
  regular functions, normalized by Gamma(Spec A) = A, not an arbitrary ring map.
- Uniqueness is the following `∀ q`, with exactly the same normalization,
  concluding `q = p`. Geometric properties are not premises of uniqueness.
- Every scheme test of the diagonal is a closed immersion via the existing
  `IsRepresentableWith (fun _ _ f ↦ IsClosedImmersion f.left)
  (pullback.diagonal p.hom.hom)`.
- Universal injectivity quantifies over every algebraic space T over Spec Z and
  every map g from T to Spec A. It asserts injectivity of
  `mapPoint (pullback.snd p.hom g.hom).hom` on the existing field-point classes
  of the actual sheaf fibre product. No representability, finite-type or field
  condition is imposed on this test T.

Dependencies read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleForget`, `structureSheaf`, `Modules`, `IsRepresentableWith`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  slice infrastructure; the hypothesis uses its underlying unchanged
  `SheafOfModules.IsQuasicoherent` predicate.
- `Sheaf.CategoryTheory.SiteCoveringAxioms` and
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: `Sheaf.H` and
  `SheafOfModules.toSheaf` implement the recorded cohomology convention.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.snd`, `pullback.diagonal`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  using `Point` from `AlgebraicSpacePointClasses`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- `Sheaf.AlgebraicGeometry.SpaceChangeBase`: `exists_spaceChangeBase`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, the already
  owned scheme-as-space construction.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `mapPoint`.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Scheme.ΓSpecIso`;
  `Mathlib.AlgebraicGeometry.Limits`: `specULiftZIsTerminal`.

The four added statement dependencies are existing landed nodes:
`def-sfb-space-absolute-quasi-separated`, `def-trf-scheme-algebraic-space`,
`def-sfb-proper-curve-moduli`, `lem-sfb-space-change-base-to-integers`. They own the
interfaces used directly in the statement and its absolute-space helper. No
mathematical statement or accepted proof split changes.

All proof dependencies with recorded modules or Mathlib matches are imported
privately unless already public for the statement: QuasiCompactH1Zero,
EtaleZariskiQcohComparison, AlgebraicSpaceH1AffineBaseChange,
AlgebraicSpaceUCSurjectionSeparation, StackUniversalInjectivityCriteria,
SchemeZariskiEtaleQuasiCoherentEquivalence, and Mathlib separatedness and
closed-immersion base change. Unrecorded proof-only nodes are retained in the
DAG and proof docstring, without inventing imports or restating them.

Edge cases checked before drafting: empty X gives the zero ring of global
functions, empty Spec A, its unique map, and injectivity from an empty point set.
The zero ring is allowed by `CommRingCat` without a Nontrivial binder. Arbitrary
nonempty affine X gives the usual identity affinization. Nonreduced rings,
non-flat scalar extensions, fields in every characteristic, and arbitrary
algebraic-space base changes are retained. No finite-type, separated-base,
Noetherian, algebraic-closedness or reducedness assumption was introduced.
The universes of all test schemes, fields and rings remain the fixed site
universe u; field-point sets have the existing universe u+1.

Sources read: Stacks `spaces-cohomology.tex`, Situation 07UY and the full proofs
of 07V4 and 07V5; `spaces-properties.tex`, full 05Z1. The theorem docstring
carries all seven accepted proof steps with their node references. No statement
fault or dispute was found.

Searches for an existing statement (msearch.py, logs in searches.jsonl):

- leanfinder: "A quasi compact quasi separated algebraic space with zero first
  cohomology of every quasi coherent module has separated universally injective
  affinization": eight scheme/affine-property results, no algebraic-space theorem.
- loogle: `"UniversallyInjective", "IsSeparated"`: zero hits.
- grep Mathlib AlgebraicGeometry: `AlgebraicSpace|acyclic.*affinization|affinization.*injective`:
  zero hits.
- leansearch: "Algebraic space vanishing first cohomology quasi coherent modules
  canonical affinization separated universally injective": eight results about
  scheme affineness or cotangent H1, no match.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `affinization.*(injectiv|separat)|acyclic.affinization|vanishing_(injective|separated)`:
  no matching declaration. Searching `affinization` and H1-related interfaces
  located the existing affine-base-change module, which is imported, not copied.
- The absolute helper's name was searched in Mathlib and both source roots:
  no existing declaration. Its mathematical construction reuses the existing
  change-of-base equivalence, rather than defining that notion again.

Validation: scompile.py compiled the module in both sandbox and library contexts
without errors or warnings (7.4 s and 3.8 s respectively). All variables and
universes are bound explicitly; every line is at most 100 characters.

## Second reading by Q46

This is a second pass by the same dispatcher-started worker, not an independent
agent review; the prompt prohibits starting other agents and assigns independent
review to the maintainer. I reopened the node and module, and checked the clause
mapping above in reverse order. In particular, arbitrary algebraic-space base
changes remain present, the diagonal uses all scheme tests, uniqueness only
assumes the identity normalization, and the original arbitrary base S remains.
The ring-cone normalization is precisely chartwise pullback of the given p,
so neither an unrelated global-ring isomorphism nor a bare arbitrary morphism
can satisfy the statement. The absolute helper selects the characterized
change-of-base equivalence; it does not choose uncharacterized data. The only
record adjustments during this pass were adding the four existing interface
owners to stmt_deps. No statement correction or dependency replacement was needed.
