## Worker report

The delivery states `AlgebraicGeometry.PGLLinearization.projective_pgl_stable_quotient`
in `Sheaf.AlgebraicGeometry.ProjectivePGLStableQuotient`. It also supplies the missing
PGL-linearization and invariant-section interfaces in
`Sheaf.AlgebraicGeometry.PGLLinearizedPolarization`, owned by the new definition node
`def-sfb-pgl-linearized-polarization`. No natural-language statement is changed and no
proof of the quotient theorem is attempted. Its proof is `sorry`. The only other
postponed theorem is `Action.invariantGrading_existsUnique`: the new definition node
explicitly states uniqueness of the inherited graded-ring decomposition, and its
complete construction/uniqueness argument is in the theorem's docstring. The grading
instance chooses only this uniquely determined grading, not an unspecified ring,
action, scheme, line module, map or quotient.

The theorem renders the hypotheses as follows:

- `k : Type u` and `[Field k]` give an arbitrary field. All schemes, fields of
  geometric values and test schemes use the same universe `u`; there is no smaller
  independent test universe and no characteristic hypothesis.
- `r : ℕ` and `hr : 1 ≤ r` give the positive matrix size.
- `Z : Over (Spec (.of k))`, `hprojective : IsHProjective Z.hom` and
  `hfiniteType : LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom` give precisely the
  specified projective finite-type k-scheme, in the finite-projective-space convention.
- `L : Z.left.Modules`, `[L.IsInvertible]` and `hample : IsAmple Z.hom L` give the
  invertible ample module. The recorded `IsAmple` definition is invertibility plus a
  positive tensor power that is the pullback of O(1) along a finite projective-space
  closed immersion. Its proper-scheme convention is exactly the one in this item.
- `D : Action k r Z L` gives the algebraic PGL action and its line linearization.
  This is written using its faithfully flat GL presentation: for EVERY k-scheme T,
  the group is GL_r(Γ(T,O_T)); the action on maps T→Z is natural in T, satisfies the
  group laws, and scalar matrices act trivially. Each line lift is an O_T-linear
  isomorphism x*L→(gx)*L; these satisfy the identity and product cocycles, the same
  scalar-kernel condition, and pullback naturality using the existing canonical
  `Scheme.Modules.pullbackComp`. By Yoneda this is an algebraic GL action. Descent
  along GL→PGL gives exactly a PGL action, because the GL scalar kernel is trivial
  on both the scheme and the line. Conversely every PGL action gives these data.
  We do NOT identify PGL(T) with GL(T)/Γ(T,O_T)ˣ on arbitrary T; those quotients need
  fppf sheafification, and the natural scalar-trivial GL presentation incorporates
  that descent. Thus test schemes with nontrivial Picard groups are retained.
- `U : Z.left.Opens` and `hsemistable` name the semistable OPEN, characterized on
  every algebraically closed extension Ω/k by `D.IsSemistable Ω x`. This predicate
  is existence of n>0 and a globally invariant section of L^n whose canonical
  pullback along x is nonzero. Invariance is tested on ALL scheme-valued points,
  so infinitesimal/nonreduced structure is retained. `powerLift` is obtained by
  recursively tensoring the specified line isomorphism and the actual monoidal
  pullback comparisons; there is no freely chosen representation on sections.
  Using base-k invariant sections agrees with geometric semistability: field
  extension is flat, global sections commute with flat base change here, and
  invariants are the kernel of the coaction defect and commute with flat extension.
- `J`, `j`, `jU`, `hclosed` and `hfactor` mean J is a closed subscheme of U and its
  composite into Z is j. This retains the scheme structure, not just a closed
  subset of geometric points.
- `hinvariant : D.IsInvariantSubscheme j` tests invariance of that subscheme on
  every test scheme T. Each translate of a T-point of J lifts back to J. Since j
  is an immersion, uniqueness follows and this is exactly factorization of the
  scheme action, not merely invariance of the reduced geometric locus.
- `hstable` says every geometric point of J is `D.IsStable` in Z. The latter includes
  semistability, orbit-closedness among the semistable points of the Ω-base change,
  and finiteness of the set of PGL classes in its GL stabilizer. Ω is explicitly
  algebraically closed when `IsStable` is used or defined. Closedness is rendered
  by a closed subset C of Z_Ω whose semistable Ω-valued points are exactly the
  orbit. For finite-type schemes over an algebraically closed field this is
  equivalent to the geometric orbit being closed in Z^ss_Ω. The finite-type PGL
  stabilizer has dimension zero iff its Ω-points are finite. Its Ω-points are the
  image of the GL stabilizer under `Matrix.ProjGenLinGroup.mk`, since over a field
  the scalar quotient is surjective. This condition permits nonreduced finite
  stabilizer schemes and adds neither freeness nor étaleness.

The conclusions are rendered as follows:

- `closureOver j` is the EXISTING `j.left.image` (scheme-theoretic image), with its
  composite map to Spec k. For this locally closed immersion it is exactly the
  scheme-theoretic closure in the node. `closureInclusion` only packages its
  existing `imageι` as a morphism over k; neither construction replaces its ideal.
- The existential `E` gives the restricted action on that closure and the actual
  module `(Scheme.Modules.pullback j.left.imageι).obj L`. `D.IsRestriction ... E`
  fixes both its action and its line lifts by their composites to Z; it is not an
  unrelated choice of linearization on the closure.
- `E.invariantRing` is the subring of the EXISTING tensor section ring generated
  by homogeneous invariant sections. Since the action preserves degree, every
  invariant element has invariant homogeneous components, so this is exactly the
  invariant graded algebra in the item. Its multiplication, unit and grading use
  `Scheme.Modules.InvertibleSectionRing`, `sectionRingGrade` and the tensor section
  multiplication, with no private replacement ring or multiplication.
- `E.IsFinitelyGenerated` is finite generation over the specified k. It says a
  finite set together with the actual structure constants generates this subring
  inside the ambient section ring. The constants are inserted using
  `Scheme.ΓSpecIso`, the scheme structure map, the existing unit-section
  equivalence and the degree-zero direct-sum injection. This is exactly algebra
  finite generation, without an arbitrary auxiliary k-algebra structure.
- `∃ d, 0 < d ∧ ∀ e, 0 < e → E.VeroneseGenerated (d*e)` supplies sufficiently
  divisible degree-one Veronese generation over the degree-zero component. The
  degree-zero component is NOT assumed equal to k; it can contain extra finite
  constants. `VeroneseGenerated m` means every degree-nm element is generated by
  degrees 0 and m inside the invariant ring. Projectivity over k is separately
  required below, so relative projectivity over the degree-zero algebra alone
  does not replace the finite-projective-space conclusion.
- `φ : k →+* E.CoefficientRing` with
  `∀ c, E.coefficientVal (φ c) = constantSection ... c` fixes the canonical
  coefficient map in degree zero. `CoefficientRing` is just a named carrier for
  `E.invariantGrade 0`, with its inherited ring instance, and `coefficientVal`
  is the two subtype projections. Naming them prevents elaboration from unfolding
  the large scheme-theoretic closure during coefficient typeclass search.
- The quotient is literally `E.projOver φ`: `Proj E.invariantGrade` with the map
  `Proj.toSpecZero ... ≫ Spec.map φ`. This is the required Proj of invariants on
  the closure, equipped with its canonical k-structure, not an abstract Q supplied
  with an unconstrained comparison.
- `q : J ⟶ E.projOver φ` is a morphism OVER k. `IsHProjective` of its target's
  structure map gives the required finite projective-space embedding, and the
  `LocallyOfFiniteType` and `QuasiCompact` conjuncts explicitly retain finite type.
- `Surjective q.left` gives scheme surjectivity. The next conjunct states
  `y ≫ j = D.act ... (x ≫ j) → y ≫ q = x ≫ q` for all scheme-valued points;
  it is precisely G-invariance of q on the invariant subscheme J.
- For EVERY `B : AlgebraicSpace (Spec (.of k))` and invariant natural transformation
  `f : yoneda.obj J ⟶ B.obj.obj`, the next conjunct gives UNIQUE
  `a : yoneda.obj (E.projOver φ) ⟶ B.obj.obj` with `yoneda.map q ≫ a = f`.
  These are exactly maps of algebraic spaces out of the represented schemes.
  Together with invariance of q this is the stated composition bijection.
  No separation, representability or scheme-atlas choice is imposed on B.
- For EVERY algebraically closed extension Ω/k, the final conjunct gives
  surjectivity on Ω-valued points and the equivalence
  `x ≫ q = y ≫ q ↔ ∃ g : GL_r(Ω), D.act ... (x ≫ j) = y ≫ j`.
  Scalar-triviality and the surjective GL(Ω)→PGL(Ω) map make this exactly the
  asserted bijection J(Ω)/G(Ω) ≃ Q(Ω); no algebraic closure or lift is fixed.

Dependency declarations read and reused:

- `Field` (`Mathlib.Algebra.Field.Defs`), from `def-weil-field`.
- `AlgebraicGeometry.IsHProjective`
  (`WeilConjectures.AlgebraicGeometry.Morphisms.Projective`), from `def-kun-projective`.
- `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`
  (`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its QuasiCompact import),
  from `def-weil-finite-type-morphism`.
- `AlgebraicGeometry.AlgebraicSpace` and its full-subcategory/sheaf encoding
  (`Sheaf.AlgebraicGeometry.AlgebraicSpace`), from `def-trf-algebraic-space`.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible`
  (`WeilConjectures.AlgebraicGeometry.Modules.Invertible`), from `def-sc-invertible-module`.
- `SectionRingComponent`, `InvertibleSectionRing`, `sectionRingGrade`, the graded
  ring and tensor multiplication instances
  (`WeilConjectures.AlgebraicGeometry.InvertibleSectionRing`), from
  `def-sc-invertible-section-ring`.
- `AlgebraicGeometry.Proj`, `projIsoSpec`, `ProjectiveSpectrum.basicOpen`
  (`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`), and `Proj.toSpecZero`
  (`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`), from `def-pc-proj`.
- `AlgebraicGeometry.IsAmple`
  (`WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`), from `def-sc-ample`,
  added to the item's statement dependencies without changing any statement.
- `Scheme.Hom.image` and `imageι`
  (`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`), from
  `def-nagata-scheme-theoretic-closure`, likewise added as an already recorded dependency.
- `Scheme.Hom.ker_pullback_snd`
  (`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`),
  from `lemma-nagata-dense-flat-pullback`, imported privately for the proof plan.
  Its source/docstring gives precisely flat preservation of the kernel/image.

Additional canonical APIs used are the module `pullbackComp`, `pullbackObjUnitIso`,
monoidal pullback, the tensor product of isomorphisms, `AlgebraicGeometry.pullbackΓ`,
`Scheme.ΓSpecIso`, and the matrix quotient. The live `PullbackUnit` source was read
through `scompile.py --source` when the initial qualification of `pullbackΓ` failed:
that declaration is in `AlgebraicGeometry`, not `Scheme.Modules`. No dependency
interface was replaced. The four new stage-1 proof inputs currently have no Lean
records, so there are no proof-module imports for those inputs yet; their ids and
arguments are retained explicitly in the quotient theorem's proof docstring.

Edge cases checked before the statement was finalized:

- Empty J (or empty Z/semistable open): its closure and invariant Proj are empty;
  the zero section ring and the map from k to its zero degree-zero ring are allowed.
  Surjectivity and the orbit condition have their correct empty meanings.
- r=1: every GL_1 test matrix is scalar, so both actions are trivial; the theorem
  reduces to the closed projective subscheme and its usual section-ring Proj.
  r=0 is explicitly excluded exactly as in the node.
- Positive characteristic, nonreduced schemes and nonreduced finite stabilizers:
  all scheme tests remain, and no linear reductivity, char-zero, reducedness,
  trivial stabilizer, free action or tame stabilizer hypothesis appears.
- Arbitrary algebraically closed extensions (not merely a fixed closure) and
  algebraic spaces with no separation condition are explicitly quantified.
- A finite degree-zero k-algebra larger than k is allowed. The Veronese generation
  condition is over degree zero, and projectivity is asserted over k itself.
- The inherited grading and its decomposition have a uniqueness proof obligation;
  the definition cannot choose unrelated graded multiplication or an unrelated ring.

Searches made:

- `msearch.py leanfinder`: "A closed invariant subscheme of a projective semistable
  locus contained in the stable locus has a projective geometric PGL quotient".
  Hits include Proj and projectivity facts but no GIT quotient statement.
- `msearch.py loogle`: "AlgebraicGeometry.Proj, Matrix.ProjGenLinGroup"; zero hits.
- `msearch.py grep`: "PGL|[Ss]emistable|[Ll]inearization|[Gg]eometricQuotient" in
  AlgebraicGeometry; only unrelated occurrences in gluing identifiers.
- For the new notion, `msearch.py leansearch`: "An action of the projective general
  linear group scheme is a general linear group scheme action with trivial scalar
  action, with an equivariant invertible sheaf". Results concern actions on
  projective points, not scheme-valued linearizations.
- `msearch.py leanfinder`: "PGL linearized invertible sheaf invariant sections
  stable and semistable loci scheme valued points". Results concern ordinary
  module sections, localization and basic opens, not GIT linearizations.
- `msearch.py loogle`: `"linearization"`. Results concern free linearizations of
  G-sets in representation theory, not line modules on schemes.
- `msearch.py grep`: "IsSemistable|Linearized|Linearization|GeometricQuotient" in
  AlgebraicGeometry; no hits. The query/result metadata are preserved verbatim
  in the new node's `mathlib_searches` and the sandbox's searches.jsonl.
- `rg` over both project roots found the general linear group scheme and the
  canonical module and section constructions but no matching GIT notion or item.
  `grep -rn` for this item's id in WeilConjectures found no statement.
- Parsing definition-node statements across dag/nodes found no existing GIT
  linearization/stability interface. `tools/blueprint_refs.py search linearized`
  returned only two unrelated module-object linearizations. The item's blueprint
  ancestor is null; the new node preserves this and prepends the item to its via.

Sources: the recorded MFK book is WANTED locally, as the source node already says.
The cited Morrison PDF (https://arxiv.org/pdf/0810.2340) was opened, including its
GIT setup and the quotient application near Corollary 11. Its application does
not by itself prove the full arbitrary-characteristic algebraic-space theorem;
this limitation remains as recorded in the node. The delivery formalizes the
reviewed node's statement and proof plan, and does not claim a new source proof.

The previous worker's "already split and reviewed" obstacle was a stage-1 routing
issue: the node now has its reviewed stage-1 split and no Lean record, exactly the
state for this stage-2 statement delivery. We preserve the live split and do not
resplit it. There is no statement dispute or dependency-interface correction.

## New nodes

`def-sfb-pgl-linearized-polarization` supplies the missing natural GL/scalar
presentation of a PGL action on a scheme and a line module, its tensor-power
linearization, invariant sections/ring/unique inherited grading, semistability,
stability, coefficient map and invariant Proj, and the invariant-subsheme/map
predicates needed to state the quotient. Its self-contained statement explicitly
states the same descent presentation, the all-test-scheme equality for invariant
sections, the geometric closed-orbit and dimension-zero criterion, the inherited
graded-ring decomposition and its uniqueness, and the finite generation/Veronese
conventions. Its source is MFK Chapter 1 §1 and Theorem 1.10, with Morrison §2/§3.3
for the setup. Searches above found no matching DAG node, Mathlib declaration or
project declaration. Existing scheme, invertible-module, section-ring, Proj and
algebraic-space declarations are reused rather than copied. All helper declarations
are listed in `lean.declarations`, with source/blueprint docstrings.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
