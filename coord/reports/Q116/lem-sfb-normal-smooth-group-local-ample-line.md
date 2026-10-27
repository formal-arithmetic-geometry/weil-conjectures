## Worker report

Stage 2, Q116, lem-sfb-normal-smooth-group-local-ample-line, 2026-10-24.

The delivery states
`AlgebraicGeometry.Scheme.Modules.exists_affine_cover_isAmple_of_normal_smooth_group`
in `Sheaf.AlgebraicGeometry.NormalSmoothGroupLocalAmpleLine`. Its entire proof is
`sorry`; no definitions or auxiliary theorems are introduced. The declaration docstring
carries the accepted six-step proof, including its dependency identifiers.

The inherited BLOCKED report concerns a stage-1 attempt to re-split an already reviewed
node. The live node is split, reviewed PASS by NJ, and has no Lean record; the current
queue lists it at stage 2. The explicit handoff in coord/brief-stage2.md section 0 applies:
the accepted split is the input, not a prohibition on stating it. This delivery preserves
that split and all its proof steps. No repair note for this item is present.

Clause-by-clause correspondence:

- The base scheme is `(S : Scheme.{u})`. The explicit universe `u` is arbitrary.
- Locally Noetherian is `[IsLocallyNoetherian S]`.
- Normality is `hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
  IsIntegrallyClosed (S.presheaf.stalk s)`: every local ring is a normal domain.
  This is stalkwise scheme normality, not global integrality; disconnected normal
  schemes are included. The conjunction uses the recorded normal-domain notions.
- The group over S is `(H : Over S) [GrpObj H]`. The generic recorded GrpObj class
  supplies multiplication, identity and inverse with the group laws in Over S.
  It works over arbitrary S, despite the field specialization in the dependency's
  explanatory prose. No commutativity assumption is imposed.
- Smooth and separated are `[Smooth H.hom] [IsSeparated H.hom]`.
- Finite presentation is `[LocallyOfFinitePresentation H.hom] [QuasiCompact H.hom]`;
  its remaining quasi-separatedness requirement follows from separatedness. This
  excludes no finitely presented separated morphism and does not replace finite
  presentation with merely local finite presentation.
- Connected fibres are `hconnected : ∀ s : S, ConnectedSpace (H.hom.fiber s)`.
  Mathlib's fibre is the pullback along Spec of the residue field. ConnectedSpace
  includes nonemptiness, as the dependency requires; for a group the identity also
  ensures each fibre is nonempty. Geometric connectedness is not substituted.
- The affine open cover is `∃ (I : Type u) (W : I → S.Opens), ...`, with
  `∀ s : S, ∃ i : I, s ∈ W i` giving the covering and `IsAffineOpen (W i)`
  giving the affineness of every member. No finiteness condition on the cover occurs.
  An index in Type u suffices: the construction chooses one neighbourhood per point
  of S, whose point type is Type u.
- The base change H_W is represented canonically by the inverse-image open
  `(H.hom ⁻¹ᵁ W i).toScheme`; `H.hom ∣_ W i` is its map to `(W i).toScheme`.
  Open restriction is the canonical base change along W_i → S.
- The line on that scheme is `R : (H.hom ⁻¹ᵁ W i).toScheme.Modules` with
  `hR : R.IsInvertible`. Its absolute ampleness is
  `@IsAmple (H.hom ⁻¹ᵁ W i).toScheme R hR`.
- The same R is relatively ample over W_i: for every affine open V of W_i, its
  restriction to the inverse image of V is invertible and absolutely ample.
  The displayed existential witness `h` supplies the proof argument for IsAmple;
  it does not quantify over a substitute line bundle. The restriction is precisely
  `(tensorPullback (((H.hom ∣_ W i) ⁻¹ᵁ V).ι)).obj R`.
  This is the established inline formulation used by SchemeRelativeAmpleBaseChange
  and SchemeAmpleCanonicalProjCriterion, and the definition in Stacks Tag 01VH.
  Both absolute and relative ampleness concern the SAME existentially chosen R.

Dependency declarations read and reused:

- def-pc-scheme: AlgebraicGeometry.Scheme and its morphisms,
  Mathlib.AlgebraicGeometry.Scheme (publicly imported through the displayed interfaces).
- pqf-def-locnoeth: AlgebraicGeometry.IsLocallyNoetherian,
  Mathlib.AlgebraicGeometry.Noetherian.
- def-sbc-smooth-morphisms: AlgebraicGeometry.Smooth,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth. The deprecated IsSmooth alias is avoided.
- def-sbc-locally-finite-presentation: AlgebraicGeometry.LocallyOfFinitePresentation,
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation. QuasiCompact comes from
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact and IsSeparated from
  Mathlib.AlgebraicGeometry.Morphisms.Separated.
- def-weil-connected-scheme: ConnectedSpace, Mathlib.Topology.Connected.Basic;
  AlgebraicGeometry.Scheme.Hom.fiber, Mathlib.AlgebraicGeometry.Fiber.
- def-sc-invertible-module: AlgebraicGeometry.Scheme.Modules.IsInvertible,
  WeilConjectures.AlgebraicGeometry.Modules.Invertible.
- def-weil-pbc-normal-ring: IsDomain and IsIntegrallyClosed,
  Mathlib.RingTheory.IntegralClosure.IntegrallyClosed. Scheme normality is written
  stalkwise as normal local domains rather than a second named normality predicate.
- def-sc-group-scheme: CategoryTheory.GrpObj,
  Mathlib.CategoryTheory.Monoidal.Grp, with cartesian group-object interfaces publicly
  imported by WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- def-weil-pbc-ample-invertible-module: AlgebraicGeometry.Scheme.Modules.IsAmple,
  WeilConjectures.AlgebraicGeometry.Ample. This is the actual absolute ample predicate
  using positive tensor powers and affine nonvanishing neighbourhoods.
- Added the already landed def-pc-module-pullback to stmt_deps because the relative
  clause explicitly uses its restriction functor. Import its recorded module
  Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction; reuse the upstream
  AlgebraicGeometry.Scheme.Modules.tensorPullback construction publicly exported there.
  No dependency record is changed and no new notion or node is added.

The modules of recorded proof dependencies are imported without public export when
only used by the proof plan: Mathlib's Proper, QuasiSeparated, IdealSheaf.Subscheme,
Topology.NoetherianSpace, and the two recorded upstream EffectiveCartier modules.
Statement modules already supply Noetherian, smooth/separated base-change,
finite-presentation permanence, group objects and invertible modules. The proof
nodes lem-sfb-group-local-minimal-prime,
lem-sfb-smooth-normal-affine-boundary-cartier,
lem-sfb-group-affine-section-ampleness, and lem-trf-affine-base-ample-canonical-data
have no lean/mathlib_match records in the read repository, so have no recorded modules
to import. They are proof inputs only, not objects required to type this statement.

Edge cases checked before writing:

- Empty S: I may be empty, and the covering and all indexed conclusions are vacuous.
  There is no Nonempty S or Nonempty I assumption. This agrees with proof step 6.
- S need not be affine, quasi-compact, integral, connected, or nonempty; the normality
  hypothesis is local and the covering can be infinite.
- The group need not be commutative or proper. An affine smooth connected group and
  an abelian scheme both fall within the hypotheses.
- For an affine group, the trivial line can be ample; the proof permits empty boundary D.
- Disconnected fibres are excluded exactly by the stated connectedness hypothesis.
- Empty affine subopens V occur in the relative clause; the restriction and the
  absolute ample predicate on the empty scheme remain meaningful.
- There is no dimension, characteristic or positive-dimensional restriction.

Searches, using the prescribed msearch.py wrappers and read-only source searches:

1. leanfinder: "A smooth separated group scheme with connected fibres over a normal
   locally Noetherian scheme admits an ample invertible module locally on an affine
   open covering of the base". Eight hits concern affine transition limits,
   normalization covers, affine descent and affine space; none states this theorem.
2. leansearch: "A smooth group scheme over a normal locally Noetherian scheme admits
   a relatively ample invertible sheaf locally on the base". Eight hits concern
   Smooth, relative dimension, and locally Noetherian schemes; no ampleness theorem.
3. loogle: `AlgebraicGeometry, IsAmple` reports unknown identifier AlgebraicGeometry
   and no hits. The follow-up quoted query `"IsAmple"` succeeds with zero hits.
4. msearch grep in Mathlib/AlgebraicGeometry:
   `(groupScheme|group scheme).*(ample|projective)|(ample|projective).*(groupScheme|group scheme)`
   gives zero hits.
5. rg over lean/WeilConjectures and lean/Sheaf for this node id,
   `group.*local.*ample|local.*ample.*group`, and the proposed declaration name gives
   no existing statement. The upstream declaration-name index also has no clash.
6. rg for IsRelativelyAmple/relativeAmple and IsAmple/tensorPullback finds the existing
   inline relative-ampleness convention in SchemeRelativeAmpleBaseChange,
   SchemeAmpleCanonicalProjCriterion and CompositionFiniteAffineTwistBounds.
   These were opened; they are permanence/characterization results, not this theorem.
7. rg for normal stalk hypotheses and GrpObj over arbitrary S confirms the existing
   inline normality and Over S encodings; no private replacement is introduced.

Sources checked: the local latest blueprint unit sk-thm-sf-ctf-stability is the six
functors context, not this auxiliary statement. The original Raynaud PDF is absent
locally; its accepted reference is preserved. Read Guo's current public PDF,
https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf, especially Corollary
6.13 and its proof (printed p.19), with Theorem 1.1 and Corollary 6.14 as context.
Corollary 6.13 applies to H acting on itself and gives the required local
quasi-projectivity. Read the local Stacks morphisms.tex lemma-characterize-relatively-ample
(Tag 01VJ), giving the affine-base absolute/relative passage. There is no mathematical
statement correction or STATEMENT-DISPUTED flag.

Validation: scompile.py Q116 lem-sfb-normal-smooth-group-local-ample-line with the delivered
Lean file passed in both sandbox and final module form, 5.3 s and 2.5 s respectively,
with no errors or warnings. Both autoImplicit and relaxedAutoImplicit are false;
all variables and universes are explicit. The only postponed proof is the named theorem.

## Second reading by Q116

Author's separate second pass over the live node and the complete file; no separate
agent was started, as the dispatcher brief forbids this. The maintainer performs the
independent review specified by this direct-delivery assignment.

Matched every base and morphism hypothesis to the explicit binders above. Confirmed
that finite presentation retains quasi-compactness, connected fibres use the actual
residue-field fibre, and normality does not impose global integrality. Matched the
existential affine open covering, invertibility, absolute ampleness and relative
ampleness to the conclusion. In particular, the relative clause restricts the very
same R via the recorded tensorPullback and quantifies over affine opens OF W_i.
Rechecked the empty-base and empty-open cases, arbitrary universe, and absence of
commutativity, properness or finite-cover assumptions. No mismatch was found and no
statement correction was made. The one additional stmt_dep records the already
landed pullback notion used explicitly by that last clause. Read the node's entire
proof alongside the docstring: all six steps and their dependency ids are retained.
The first compiler run passed without a repair.
