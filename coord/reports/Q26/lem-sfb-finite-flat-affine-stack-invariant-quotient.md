## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteFlatAffineStackInvariantQuotient` states
`CategoryTheory.finiteFlatAffineStack_invariant_quotient`, with `sorry` as its entire
proof. It adds no definitions or helper theorems. The node is unchanged except for `lean`.

Source read: `literature/stacks-project/stacks-more-morphisms.tex`,
`lemma-well-nigh-affine` (0DUM), `lemma-well-nigh-affine-moduli-space` (0DUP),
`lemma-moduli-space-finite-affine` (0DUR), and `definition-categorical-quotient` (0DUG).
In particular, 0DUP first proves categoricality for affine targets, while 0DUR upgrades
this to all algebraic spaces. The statement includes this upgrade, as the node requires.
The docstring carries all eleven proof steps, including the construction of the relative
S-structure independently of the factorization argument.

Hypothesis and conclusion correspondence:

- Base scheme and sizes: `{S : Scheme.{u}}`, explicit universes `u v w v' w'`,
  and `A : BasedCategory.{v, w} (Over S)`. The underlying category is genuinely over
  schemes over S, with all morphisms over S. No affine, separated, field, Noetherian,
  characteristic, finite-type or nonempty assumption is made on S.
- Deligne--Mumford hypothesis: `hA : IsDeligneMumfordModuliStack A`, the recorded
  definition comprising stack descent, algebraic-space diagonal, and surjective etale atlas.
- Affine cover scheme: `U : Over S` and `hU : IsAffine U.left`.
- The cover map: `a : BasedFunctor (discreteModuli (yoneda.obj U)) A`.
  This is a morphism of the actual fibred groupoids, retaining automorphisms.
- Finite, flat, locally finitely presented, representable, surjective cover: `ha` is
  `ModuliSchemeTest (fun _ _ p ↦ IsFinite p ∧ Flat p ∧
  LocallyOfFinitePresentation p ∧ Surjective p) a`. Each scheme base change is
  represented by a scheme with the specified actual projection. This is precisely
  the finite-map scheme-test convention in the node: finite maps of algebraic spaces
  are representable by schemes. The simultaneous test retains all four properties
  on the same projection, rather than introducing an unrelated map.
- `R = U ×_A U`: existential `R : Over S` and `e` into `moduliTwoFiberProduct a a`,
  with `e.toFunctor.IsEquivalence`. The two `ModuliTwoIso` clauses identify its
  projections with the actual scheme maps `s t : R ⟶ U`. These comparisons are over S.
- Affineness of R: `IsAffine R.left`.
- Finite local freeness: `s.left.IsFiniteLocallyFree ∧ t.left.IsFiniteLocallyFree`.
  This is the recorded finite/flat/locally-finite-presentation class; on affine schemes
  it is equivalent to finite projectivity of the coordinate module (Stacks 02KB and
  00NX, exactly as the node's proof step 1 specifies). No constant rank or globally
  free basis is required; those would strengthen the assertion.
- `B = Γ(U,O_U)`: the ring in `Subring Γ(U.left, ⊤)` is the actual global-section ring.
- Invariant ring C: the existential subring is constrained by
  `C = RingHom.eqLocus s.left.appTop.hom t.left.appTop.hom`. Mathlib's `eqLocus`
  has carrier exactly `{b | s* b = t* b}`. Its subring structure and subtype inclusion
  are existing concrete constructions, not postponed data or a chosen quotient ring.
- `M = Spec C` with an S-structure: `σ : Spec (.of C) ⟶ S`, so its relative object
  is `Over.mk σ`. Its underlying scheme is literally the required spectrum.
- Map from U induced by the inclusion: `φ : U ⟶ Over.mk σ` and
  `φ.left = U.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom C.subtype)`.
  The first factor identifies affine U with the spectrum of its actual global functions;
  the second is contravariantly induced by the literal invariant-subring inclusion.
  Because φ is an Over morphism, it also imposes the required structural compatibility.
- Quotient map: `q : BasedFunctor A (discreteModuli (yoneda.obj (Over.mk σ)))`.
  `Nonempty (ModuliTwoIso (a.comp q) (discreteModuliMap (yoneda.map φ)))`
  states its prescribed composite on the atlas. Equality of stack morphisms is expressed
  by the appropriate vertical 2-isomorphism.
- Uniform categoricality: for every algebraic space M₁ over S and map b to M,
  flatness is tested on all etale scheme charts c via
  `Flat (yoneda.preimage (c ≫ b)).left`. For every algebraic space Z/S the displayed
  `Function.Bijective` is precisely precomposition with the projection
  `moduliTwoFiberFst (discreteModuliMap b) q` from the actual 2-base change. Its domain
  is all natural transformations `M₁.obj.obj ⟶ Z.obj.obj`, namely Hom_S(M₁,Z),
  and its codomain is all based functors from that 2-base change to discrete Z.
  Thus this asserts existence and uniqueness, for all spaces and all flat space tests.
- Separatedness: `ModuliSchemeTest @IsProper (moduliRelativeDiagonal q)` uses the
  actual relative diagonal and proper scheme tests. For a DM source this is exactly
  properness of its algebraic-space diagonal: a proper unramified space map is finite
  and representable by schemes. No representability assumption is imposed on q itself.
- Quasi-compactness: `IsQuasiCompactModuliMap q` is the established DM-stack notion.
  It tests every affine scheme base change by existence of a quasi-compact etale
  scheme atlas. For a DM stack this is equivalent to quasi-compactness of the underlying
  point space. Finite affine covers of any quasi-compact open of any scheme test give
  the node's stated inverse-image criterion. This uses the existing predicate rather
  than making a second definition of quasi-compactness.
- Universal homeomorphism: every algebraic stack
  `T : BasedCategory.{max u v v', max (u + 1) w w'} (Over S)` and every map b to M
  has `IsHomeomorph (moduliPointMap (moduliTwoFiberFst b q))`.
  The stack test universes include the base and source sizes and permit arbitrary
  enlargement by v',w'. Tests are all algebraic stacks, including those with smooth
  atlases that are not DM. Points and topology are the existing field-object quotient
  and smooth-atlas topology; no arbitrary point map or topology is supplied.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (nodes def-pc-scheme and def-weil-affine-spectrum).
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsDeligneMumfordModuliStack`, `discreteModuli`, `discreteModuliMap`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `ModuliTwoIso` (the recorded declarations
  of def-sfb-stable-pointed-moduli-groupoids). Their full source definitions were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsEtale` (def-trf-algebraic-space).
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`
  (def-weil-finite-integral-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`
  (def-weil-flat-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (def-sbc-locally-finite-presentation).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`
  (def-weil-proper-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (def-sbc-smooth-morphisms), through the existing smooth-atlas definition.
- def-weil-size-convention is a convention record; it is rendered by the explicit
  universes and the enlarged arbitrary-stack tests, not a new object or hypothesis.
- Existing additional interfaces read and reused:
  `Sheaf.AlgebraicGeometry.DmStackMorphismProperties` (`ModuliSchemeTest`,
  `moduliRelativeDiagonal`, `IsQuasiCompactModuliMap`, `ModuliPoints`, `moduliPointMap`);
  `Sheaf.AlgebraicGeometry.OpenModuliSubstack` (`moduliTwoFiberSnd`);
  `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`
  (`moduliPointTopologicalSpace`, reexporting `IsAlgebraicModuliStack` from
  `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`);
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`
  (`Scheme.Hom.IsFiniteLocallyFree`);
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction` (`Scheme.toSpecΓ`);
  `Mathlib.Algebra.Ring.Subring.Basic` (`RingHom.eqLocus`).
  These are imports of established notions, with no interface repair or new definitions.

All proof dependencies with recorded source modules are imported as ordinary (non-public)
imports unless already public because needed in the statement. No proof-only import cycle
was encountered. Dependencies which are Mathlib leaves without `lean.module` are available
through the statement imports where needed; no new postponed theorem is introduced.

Edge cases checked before and after writing:

- Empty U: surjectivity forces A empty; R and the invariant spectrum are empty. The
  zero ring is allowed by `Subring`, `CommRingCat.of`, and `Spec`; no Nontrivial binder.
- Empty base S is permitted, and no chosen base point or field extension is required.
- Nonempty U need not be connected or reduced. Finite locally free ranks may vary;
  no positive rank or rank-one assumption appears.
- Nontrivial finite stabilizers are retained by BasedCategory and by the 2-fibre
  relation. q is not incorrectly assumed representable or an isomorphism of stacks.
- Arbitrary S is permitted, including nonaffine and nonseparated bases. The affine
  scheme M is given an arbitrary structural morphism σ, never assumed affine over S.
- Flat base changes include identities, empty spaces and non-affine algebraic spaces;
  targets Z are arbitrary algebraic spaces rather than just schemes or affine schemes.
- Arbitrary algebraic-stack tests include non-DM stacks and the identity base change.
  Their universe bound cannot be smaller than the underlying scheme site or A.

Searches (all through the prescribed tools and read-only source searches):

- msearch leansearch: "A stack with a finite flat affine scheme cover has a uniform
  categorical moduli space equal to the spectrum of its invariant ring". Eight results
  concern affine covers/spectra; none states the stack quotient theorem.
- msearch leanfinder: "Deligne Mumford stack finite flat affine cover invariant ring
  uniform categorical moduli space". Eight affine-cover/finite-affine results; no match.
- msearch loogle: "AlgebraicGeometry.IsFinite, AlgebraicGeometry.Flat". Eight finite-flat
  rank lemmas; confirms existing scheme classes but gives no stack quotient theorem.
- msearch grep: "IsUniformCategorical|FiniteFlatAffine|ModuliStack". Zero Mathlib hits.
- rg in `lean/WeilConjectures` for the node id: no existing declaration. Searches for
  invariant quotient and stack property names found scheme universal-homeomorphism
  interfaces but no theorem with this arbitrary-base stack statement.
- rg in `lean/Sheaf` found the established stack morphism and topology modules above,
  and `AlgebraicGeometry.finiteFlatAffineGroupoid_moduli` in
  `Sheaf.AlgebraicGeometry.FiniteFlatAffineGroupoidModuli`. That theorem starts with
  an explicit affine groupoid over a field and a specified quotient presentation;
  it does not state the present theorem for an arbitrary S and finite flat stack cover.
  It also has extra structure-sheaf/base-change conclusions. It is therefore not an
  exact existing match. Its source was read to check the common categorical and
  arbitrary-stack test conventions.
- rg of Mathlib Subring sources identified `RingHom.eqLocus` and its exact carrier;
  it is used directly, with no duplicate invariant-ring definition.

Validation: scompile.py compiled this single delivered module cleanly against the live
published library (sandbox check 6.6 s; library check 7.0 s). No warnings or errors.
No statement correction, statement dispute, dependency repair or new DAG node was needed.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
