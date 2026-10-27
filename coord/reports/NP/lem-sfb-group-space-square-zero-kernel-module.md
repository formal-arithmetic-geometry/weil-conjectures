## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.groupSpace_squareZero_kernel_module`
in `Sheaf.AlgebraicGeometry.GroupSpaceSquareZeroKernelModule`. Its sole theorem has
proof `sorry`. All helper definitions have explicit data. The additional definition
module constructs relative differentials using the existing ringed-site differential
sheaf and existing canonical structural ring map. No statement correction or dispute.

Hypothesis and clause correspondence:

- The scheme S is the explicit namespace variable `{S : Scheme.{u}}`. The algebraic
  space is `(G : AlgebraicSpace S)`, precisely the dependency's existing definition.
- A group algebraic space, including its multiplication, inverse, identity and laws,
  is encoded by the group-valued functor `F : (Over S)ᵒᵖ ⥤ GrpCat.{u}` and the
  isomorphism `e : F ⋙ forget GrpCat ≅ G.obj.obj`. This is the existing encoding
  used by `exists_groupScheme_of_locallySeparated`. This imposes neither
  commutativity nor smoothness. Yoneda identifies points with morphisms, and
  `groupPointMap` makes that identification explicitly.
- The affine test is `Over.mk s` for `s : Spec (.of A) ⟶ S`, with `A : Type u` and
  `[CommRing A]`. `I : Ideal A` gives `quotientTest s I = Spec(A/I)` over S and
  `quotientTestArrow s I` is Spec of the quotient homomorphism. The hypothesis
  `IsFirstOrderThickening (quotientTestArrow s I).left` is exactly the recorded
  closed-immersion square-zero-ideal condition, hence I²=0 in these affine models.
  Using that predicate instead of repeating `I ^ 2 = ⊥` adds no hypothesis.
- The original kernel K is `squareZeroPointKernel F s I`, literally the kernel
  subgroup of the restriction group homomorphism `F.map (quotientTestArrow s I).op`.
  Its identity, multiplication, inverse and powers are the original group operations.
- `relativeOmega G` is Ω¹_(G/S). It is constructed on the existing equivalent
  small affine model, then transported back to the original small etale site.
  `relativeOmegaSection` is the actual universal differential on every basis chart.
- `differenceIdeal j` is the kernel of the existing structure-module map
  O_T → j_*O_T0. `differenceIdealOnReduction j` is its actual tensor pullback,
  namely I/I², identified with the ideal I in the square-zero situation. This is
  the canonical associated ideal module on the small etale site, not an arbitrary
  coefficient sheaf or an extra choice. No finite-presentation hypothesis is used.
- The identity point `groupPointMap G F e (Over.mk s) 1` is e_T. Composing with
  `groupSchemeMap j` is e_0. `differenceHom j e_T` is precisely
  `Hom(e_0^* relativeOmega G, differenceIdealOnReduction j)`, using the existing
  tensor inverse-image functor with its adjunction and section normalization.
- `∃! δ : K ≃ differenceHom ...` asserts the canonical bijection. The predicate
  `IsSquareZeroDifference` fixes it on universal differentials by b-sharp minus
  e_T-sharp. Concretely, for a source etale chart U, its entire cartesian reduction U₀, and maps α, β having the
  same reduction, the kernel section s has inclusion β*(x)−α*(x); δ(b) takes the
  local tensor of dx to the local tensor of this s. The tensor sections are the
  existing adjunction-unit tensors. This sign and section formula exclude an
  arbitrary unnormalized equivalence. Common etale refinements exist because a
  square-zero closed immersion induces the equivalence of etale sites; affine
  target charts and their universal differentials generate the entire sheaf.
- `δ 1 = 0` and `∀ x y, δ (x*y) = δ x + δ y` assert exactly preservation of
  identity and products. Together with the equivalence they give the additive
  group isomorphism, with `Additive K` understood if it is bundled as `≃+`.
- The existential `C : AddCommGroup K` and `M : Module (A ⧸ I) K` explicitly
  supply the asserted module structure on the original underlying kernel type.
  `C.zero = 1` and `C.add x y = x*y` retain the original group law as addition.
  The displayed componentwise scalar formula fixes the transported scalar action:
  on each etale chart, δ(c·x)(v) = c|_U δ(x)(v). `quotientChartScalar` is actual
  pullback of a scalar along the represented scheme map, via `Scheme.ΓSpecIso`.
  As δ is normalized uniquely, this component formula determines the action
  uniquely. Thus this is a canonical module structure, not merely its existence.
- The last clause quantifies over every `r : ℕ` and every x and states
  `(r : A ⧸ I) • x = x ^ r` for that module structure. This covers precisely
  every nonnegative integer, including zero.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`;
  locally ringed spaces locally affine and their actual morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `structureSheaf`, `Modules`. The space is the full subcategory of
  fppf sheaves with representable diagonal and an etale surjective scheme atlas.
- `WeilConjectures.AlgebraicGeometry.Thickening`: `IsFirstOrderThickening`, whose
  full body is `IsClosedImmersion i ∧ i.ker ^ 2 = ⊥`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  a transparent abbreviation for Mathlib `SheafOfModules`, inherited by Modules.
- `Sheaf.AlgebraicGeometry.RegularGroupSpace`: only `groupSpaceBase`,
  `groupSpaceProjection`, `groupSchemeMap`. Its `CommutativeSpaceGroup` was read
  and deliberately not used to impose a commutativity hypothesis on the theorem.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`: `cotangentRingMap` and its
  normalized inverse-image structural map on the existing small affine models.
- `Sheaf.CategoryTheory.Sites.InverseImageDifferentials`:
  `CategoryTheory.SheafDifferentials.omega` and `.derivation`; these sheafify
  Mathlib sectionwise differentials, retaining the universal derivation.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`:
  `smallModuleEquivalence`, `smallEtaleInclusion`, `smallStructureSheaf`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleTensorPullback`, `moduleTensorSection`, `ModuleChart`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap`: `moduleStructureMap`.
- The proof prerequisite `lem-sfb-space-square-zero-lift-linearization` currently
  has no Lean record, so there is no proof-only module to import. The theorem's
  docstring contains all four proof steps and names that prerequisite explicitly.
  The statement does not depend on a chosen bijection from an unstated theorem.

Source reading: spaces-more-morphisms.tex Tags 0618, 0619 and 04D0, including their
proofs, and groupoids.tex Tag 0BF5 including the linearity-and-unit proof. The
relative differential construction follows spaces-more-morphisms.tex Tag 04CT
and sites-modules.tex Tag 04BN. The construction of differential generators uses
the already normalized structural map, with no new ringed-topos hypotheses.

Edge cases checked before and after writing: I=0 gives the trivial kernel and
zero coefficient module; A the zero ring gives the empty affine test and the same
trivial groups. The trivial group space gives zero differential Hom. For G_a the
identification is the ordinary additive ideal I; for G_m the expansion
(1+x)(1+y)=1+x+y uses xy=0. For noncommutative G the proof uses only linearity of
multiplication and its two unit laws. Characteristic p makes the pth power on K
trivial exactly as scalar p is zero. The r=0 clause is zero action equals the
identity element. No affineness, local finite presentation, separatedness,
smoothness or commutativity of G is required. The scheme and coefficient universe
is the existing algebraic-space convention u, and the small-model equivalence
keeps that original universe; no extra universe equality is added.

Searches performed with msearch.py (all exact queries and returned metadata are
also recorded in the new definition node's mathlib_searches):

- LeanFinder: "Kernel of group algebraic space points across square zero thickening
  is canonically module Hom of relative differentials". Eight ring-level hits,
  including `Algebra.Extension.ker_infinitesimal`, `KaehlerDifferential.ker_map`
  and `derivationQuotKerSq`; none is the algebraic-space theorem.
- Loogle: "derivationToSquareZeroEquivLift, GroupObj, KaehlerDifferential".
  Zero hits (unknown GroupObj); the existing group-valued-functor encoding was
  instead found and read in `LocallySeparatedGroupSpaceScheme.lean`.
- Mathlib grep: `squareZero.*[Kk]ernel|[Gg]roup.*[Dd]erivation|[Kk]ernel.*[Dd]ifferential`
  under AlgebraicGeometry: zero hits.
- LeanSearch: "Sheaf of relative Kahler differentials of an algebraic space
  represents derivations". Hits are sectionwise differentials and derivations;
  the project already wraps their sheafification in `SheafDifferentials.omega`.
- LeanFinder: "Sheaf of relative Kahler differentials of algebraic space over
  scheme on small etale site constructed from inverse image of base structure
  sheaf". Eight hits, all ring or presheaf constructions, not the specialization.
- Loogle: `AlgebraicGeometry.AlgebraicSpace.relativeDifferentials`: zero hits.
- Mathlib grep `AlgebraicSpace|relativeDifferentials` under AlgebraicGeometry:
  zero hits. Project rg over WeilConjectures and Sheaf found no `relativeOmega`,
  `IsSquareZeroDifference`, `differenceHom`, `groupPointMap` or `quotientTest`.
  The required node-id grep in WeilConjectures found no existing attachment.
- Scanned DAG definition statements for algebraic space and differential:
  `def-sc-relative-differential-sheaf` is scheme-only;
  `def-sfb-space-naive-cotangent-complex` constructs the two-term complex and
  does not define this relative differential module. Read both complete statements.
- `tools/blueprint_refs.py search square zero differential` returned three
  unrelated blueprint nodes (def-kun-bc-property, def-kun-truncations,
  sbc-def-base-change-map). The ancestor command gives a null blueprint ancestor,
  inherited in the new node with the item's entire existing via path.

Validation: both modules compiled separately using scompile.py against the current
server library, including the sibling-module overlay, with no errors or warnings.
No global or local Lean build was run. Auto-implicit and relaxed auto-implicit
binding are disabled explicitly in both files; every universe and variable is bound.

## New nodes

`def-sfb-space-relative-differentials` specializes the existing canonical structural
map and the existing ringed-site differential construction to an algebraic space
over its scheme base, then transports its module and differential sections through
the fixed basis equivalence. Source: Stacks 04CT and 04BN. Its three definitions
contain real data and no postponed proofs. Searches above and in mathlib_searches
found no existing specialization or DAG definition of this notion. The item's
stmt_deps adds exactly this new definition node. No dependency record is changed.

## Second reading by NP

No independent second worker was started, in accordance with the dispatcher brief.
The maintainer's independent review is the delivery review. On my own fresh reading
of the node and both modules, I checked every hypothesis and clause against the
correspondence above, including the sign β*−α*, the identity-point origin, the
reduction coefficient I/I²=I, the original multiplicative kernel operations, the
componentwise A/I action, uniqueness of the normalized equivalence, and r=0.
The source citation of the new construction was corrected to 04CT and 04BN.
The fresh reading found that the normalization must require U₀ to be the entire
cartesian reduction of U. Without this requirement, an empty U₀ would allow
different sheets of an etale target chart and falsely require their function
difference to lie in the ideal. Added the explicit `_hcart : IsPullback ... j`
binder to `IsSquareZeroDifference`. This repairs the normalization to the source
formula; no node statement changed. No mismatch remains identified.
