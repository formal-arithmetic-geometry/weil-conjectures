## Worker report

The module `Sheaf.AlgebraicGeometry.FlatAffineActionStackPresentation` states only
`AlgebraicGeometry.SchemeAction.flat_affine_action_stack_presentation`, with proof
`sorry`. All invariant-ring data and maps are imported from the existing public
module `Sheaf.AlgebraicGeometry.AffineActionStackPresentation`. No helper notion
or proof obligation is copied, renamed or redeclared.

The mathematical node statement and proof are unchanged. The saved packet's
statement dependencies and surjectivity definition record are retained; the item
additionally cites the new definition record for the existing invariant-spectrum
construction. No theorem conclusion supplies data to the statement.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Field k | `(k : Type u) [Field k]` |
| Finitely generated commutative k-algebra E | `(E : Type u) [CommRing E] [Algebra k E] [Algebra.FiniteType k E]` |
| Affine group scheme H of finite type | `H : Over (Spec (CommRingCat.of k))`, `[GrpObj H]`, `[IsAffineHom H.hom]`, `[LocallyOfFiniteType H.hom]`, `[QuasiCompact H.hom]` |
| Rational H-action and specified left-action convention | `[ModObj H (affineActionScheme k E)]`, the equivalent affine scheme-action data; the right action dual to rho is obtained by composing this left action with inversion and swapping the factors |
| U = Spec E | `affineActionScheme k E`, whose underlying scheme is literally `Spec (.of E)` |
| E^H = {e : rho(e)=e tensor 1} | `affineInvariants k E H`, the `RingHom.eqLocus` of action and projection on functions in E |
| Y = Spec E^H | `affineInvariantSpectrum k E H`, with constants restricted from the original algebra map |
| Objects are fppf locally trivial scheme H-torsors with equivariant map to U | `SchemeAction.torsorGroupoid H (affineActionScheme k E)`; `TorsorObject` and `IsLocallyTrivial` use left translation, actual schemes and the big fppf covering sieve |
| Arrows are equivariant isomorphisms preserving the map | In each fibre `TorsorHom` is an equivariant cartesian map over the identity, hence an isomorphism; it retains the map to U |
| X algebraic | First conjunct `IsAlgebraicModuliStack` of that actual torsor category |
| X quasi-compact | Second conjunct `IsQuasiCompactModuli` |
| X quasi-separated | Third conjunct `IsQuasiSeparatedAlgebraicModuliMap (moduliBaseStructure X)`; this uses the prescribed non-DM stack definition |
| X affine diagonal | Fourth conjunct `ModuliSchemeTest @IsAffineHom (moduliRelativeDiagonal (moduliBaseStructure X))` |
| Trivial torsor defines pi | Existing `quotientAtlas H (affineActionScheme k E)` |
| pi representable | `IsRepresentableByAlgebraicSpaces` |
| pi faithfully flat | `ModuliSpaceTest @Flat` together with `IsSurjectiveModuliMap` |
| pi locally finitely presented | `ModuliSpaceTest @LocallyOfFinitePresentation` |
| Every algebraic-stack base change has open surjective point map | Universal quantification over `Z : BasedCategory.{v,w} (Over (Spec (.of k)))`, `g : BasedFunctor Z X`, and `IsAlgebraicModuliStack Z`, followed by `IsOpenMap` and `Function.Surjective` for the actual `moduliTwoFiberFst g pi` |
| Invariant map descends to phi | `∃ φ : BasedFunctor X (discreteModuli (yoneda.obj Y))` |
| phi pi equals the map induced by invariant inclusion | `Nonempty (ModuliTwoIso (pi.comp φ) (discreteModuliMap (yoneda.map (affineInvariantProjection k E H))))`; the invariant inclusion is literally Spec of the equalizer subring inclusion |
| phi quasi-compact and quasi-separated | `IsQuasiCompactAlgebraicModuliMap` and `IsQuasiSeparatedAlgebraicModuliMap` of this same phi |
| Underlying point space and topology | Existing `ModuliPoints`, `moduliPointMap` and `moduliPointTopologicalSpace`, using field objects and common-extension isomorphisms, with the smooth-atlas final topology |
| No smoothness or finite-generation of invariants | No `[Smooth H.hom]` and no finite-type hypothesis on `affineInvariantRing`; the smooth-only convenience `affineActionQuotientStack` is never used |

The affine scheme action is an equivalent presentation of exactly the node's
coaction, not a restriction to abstract group actions on rational points. `ModObj`
is an actual morphism H times U to U with unit and associativity diagrams. On affine
schemes its coordinate map is a k-algebra map. If a is this left action, the right
action is b(u,h)=a(h inverse,u), so its pullback rho has the precise order E tensor C
and satisfies the stated coassociativity and counit identities. Conversely the node's
formula reconstructs a. This is reversible for noncommutative H. Applying the
inversion automorphism to the H coordinate preserves equality with the projection,
so the two invariant equalizers coincide. No additional coaction, group law or action
is chosen by a postponed existence theorem.

The diagonal and quasi-separatedness are formulated over k. These are equivalent
to their absolute versions here: Spec k is separated over Spec Z, since the ring
map k tensor_Z k to k is surjective. The absolute Isom test is the relative affine
Isom test on the closed equalizer of the two structural maps to Spec k. Composing
an affine morphism with this closed immersion remains affine. The node's proof
contains this same absolute-diagonal argument.

The qcqs predicate for phi explicitly names all seven universes: the base scheme,
the two endpoint categories, and two freely variable extra test universes. The
arbitrary base-change assertion has independent `v,w`. There is no automatic
implicit variable or generated universe left. All schemes and algebras lie in a
common arbitrary `u`, as required by the big-site convention; this imposes no
equality of previously independent site object and morphism universes.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`; the action diagrams are
  `ModObj` in `Mathlib.CategoryTheory.Monoidal.Mod` and its Cartesian specialization.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, `Scheme.ΓSpecIso`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; `GrothendieckTopology.over` supplies the slice site.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` from its quasi-compact morphism import, the recorded conjunction.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`: `IsQuasiCompactModuli`,
  `IsQuasiCompactAlgebraicModuliMap`, `IsQuasiSeparatedAlgebraicModuliMap`.
- `Sheaf.AlgebraicGeometry.SchemeActionTorsorGroupoids`: `torsorGroupoid`,
  `TorsorObject`, `TorsorHom`, `IsLocallyTrivial`, `trivialTorsorFunctor`.
- `Sheaf.AlgebraicGeometry.AffineActionQuotientStack`: `affineActionScheme`,
  `quotientAtlas`. These generic declarations have no smoothness assumption.
- `Sheaf.AlgebraicGeometry.RelativeModuliInertia`: `moduliBaseStructure`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSchemeTest`,
  `ModuliSpaceTest`, `moduliRelativeDiagonal`, `ModuliPoints`, `moduliPointMap`.
  These particular definitions impose no DM condition.
- `Sheaf.AlgebraicGeometry.ModuliChartNormalization`: `IsSchemeModuliBaseChange`.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`: `moduliPointTopologicalSpace`.
- `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`: `IsSurjectiveModuliMap`.

- `Sheaf.AlgebraicGeometry.AffineActionStackPresentation`: `affineInvariants`,
  `affineInvariantConstants`, `affineInvariantSpectrum`, `affineInvariantProjection`,
  `affineCoordinateCoaction` and `affineCoordinateInclusion`. These definitions
  precede the smoothness and finite-type binders of its main theorems.

Available proof dependencies are imported privately, except where their declarations
are also used in the public statement. The unstated proof nodes
`lem-sfb-flat-groupoid-algebraic-quotient`,
`lem-sfb-affine-group-torsor-stackification`,
`lem-sfb-algebraic-stack-fibre-products`,
`lem-sfb-representable-stack-fppf-locality`, `lem-sfb-stack-point-topology`,
`lem-sfb-algebraic-stack-quasicompact-surjection`, and
`lem-sfb-algebraic-stack-qcqs-permanence` have no usable module to import; their
proof uses remain explicitly named in the main theorem docstring.

Edge cases checked mathematically: E=0 gives empty U and X, and the zero equalizer
ring gives empty Y; all assertions include that case. For trivial H the equalizer
is E and phi is the identity under the torsor equivalence. For H=alpha_p or mu_p
in characteristic p, H is flat but may be non-smooth; no smoothness binder excludes
these examples. No characteristic restriction appears. Infinite-dimensional E as
a k-vector space is permitted; only finite generation as an algebra is required.
Non-finitely-generated E^H is permitted. H need not be commutative. Empty base
changes and the identity base change of pi are both included. The theorem's
existential phi is fixed by its composite with the fppf presentation into the
discrete target, not an arbitrary unrelated map.

Searches for the original theorem are retained in the item's `mathlib_searches`
and `searches.jsonl`: LeanFinder on an affine action quotient for a flat finite-type
group, Loogle on AlgebraicGeometry/fppf, Mathlib grep on
`quotientStack|flatGroupoid|actionStack`, and LeanSearch on the fppf presentation.
They found fppf-site and scheme-morphism infrastructure, not this theorem.

The repair searched LeanSearch for the invariant subring as coaction equalizer,
LeanFinder for the scheme-action equalizer, and Mathlib grep for
`affineInvariants|affineInvariantSpectrum|affineInvariantProjection`. The first
returned eight abstract group-invariant subring hits; the second eight abstract
representation/group-invariant hits; grep found none in Mathlib. Project grep
found the existing public equalizer, spectrum and projection in
`AffineActionStackPresentation.lean` (lines 77, 145 and 159). DAG grep found their
record only among helpers of `lem-sfb-affine-action-stack-presentation`, with no
separate definition node. `blueprint_refs.py search 'invariant ring'` found zero
blueprint nodes. The complete service outputs are recorded verbatim in the new
node's `mathlib_searches`. Read Stacks `examples-stacks.tex` Situation
`situation-quotient-stack` and Tag 04WM: its action and projection are precisely
the maps whose coordinate equalizer is used here.

## Returned delivery repair

The immutable returned head `3e9143fcd3ee` reported duplicate declarations
`AlgebraicGeometry.SchemeAction.affineInvariantConstants` and
`AlgebraicGeometry.SchemeAction.affineInvariantSpectrum`. The required initial
saved-packet dry run was checked before editing: it passed at `28673eeee50`.
That result did not remove the independently reported collision.

Compared the retained packet with current main's node and existing presentation
module. Removed all six local invariant construction declarations, including the
two colliding names and the equivalent equalizer, membership proof, inclusion
compatibility proof and inclusion map. Publicly import the existing presentation
module, use its `affineInvariants` and `affineInvariantSpectrum`, and replace the
main theorem's `affineInvariantInclusion` by the existing
`affineInvariantProjection`. The former equalizer used functions on H times U;
the existing one uses U times H after the canonical symmetry. Pullback by that
isomorphism is injective, so the equalizer subring and its canonical inclusion
are the same. This is reuse of the existing notion, with no new hypothesis.
The Lean record now lists only the main theorem and its verbatim new signature.
The delivery wrapper rebases the packet on current main.

The previous H2 repair is retained: topology and surjectivity are cited through
`def-sfb-stack-point-topological-space` and `def-sfb-surjective-moduli-map`,
respectively, rather than theorems whose modules happen to define them. The new
invariant-spectrum record follows the same rule.

## New nodes

`def-sfb-surjective-moduli-map` retains the saved `existing: true` record for
`CategoryTheory.IsSurjectiveModuliMap` in
`Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`. It specifies each
field-valued target object's lifting after a field extension with its actual
2-isomorphism. Source: Stacks Tags 04XI and 04ZS. The node records the original
LeanSearch, LeanFinder, Mathlib/project/DAG grep and blueprint searches, which
found the existing predicate but no definition node owning it. No module is added.

`def-sfb-affine-action-invariant-spectrum` records the existing coordinate
equalizer, restricted constants, spectrum and Spec-of-inclusion map, using
`existing: true` on `Sheaf.AlgebraicGeometry.AffineActionStackPresentation`.
Its data are given by `affineCoordinateCoaction`, `affineCoordinateInclusion`,
`affineInvariants`, `affineInvariantConstants`, `affineInvariantSpectrum` and
`affineInvariantProjection`. Source: Stacks Situation `situation-quotient-stack`
and Tag 04WM, by the affine coordinate equalizer construction. The searches above
found the definitions as helpers of a theorem node, with no definition node of
this construction. This record supplies the missing DAG owner without adding or
moving a Lean declaration. Its statement requires a field, a commutative algebra,
a group scheme and its action, defines the two coordinate maps on U times H,
takes their actual equalizer subring, restricts constants, and applies Spec to
its inclusion. Each clause is exactly the corresponding existing definition.
It assumes neither smoothness nor finite generation. For trivial H the equalizer
is E; for E=0 its spectrum and source are empty; nonsmooth groups are included.

## Second reading by Q87

Self-check with the node, final module, both new definition records and the
existing invariant definitions open; no second agent was started, as required by
the dispatched repair brief. The table above was rechecked against the complete
main signature. The field, finite-type algebra, affine finite-type group scheme,
actual scheme action and all nine presentation/descent clauses remain present.
The independently variable test universes and the seven explicit qcqs universes
remain unchanged. Reusing the swapped-factor equalizer and its canonical Spec
projection changes no mathematical object. No smoothness, group commutativity,
nonemptiness or finite generation of invariants was introduced. The final module
contains exactly one theorem, with `sorry` proof, and declares no invariant helper.

For surjectivity, every field K, its base structure and target object has a field
extension L/K, an object over the specified composite base structure, and the
actual 2-isomorphism after restriction. Empty target and identity maps retain the
usual conventions. For the invariant-spectrum node, the variable binders of the
imported definitions are exactly k, E, their field/ring/algebra structures, H,
GrpObj H and ModObj H U. Neither main theorem in the imported file is invoked.
No mismatch remains and no mathematical statement correction was necessary.

Repair validation: `scompile.py` compiled the final file separately under its
sandbox and final library names with no errors or warnings (11.8 s and 4.9 s).
A long module-docstring line found in the first run was wrapped and recompiled.
Checked that the Lean record's signature is verbatim, all lines are at most
100 columns, exactly one `sorry` theorem remains, and the mathematical node
statement, proof and proof dependencies match current main unchanged.
