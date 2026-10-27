## Worker report

Stage 2, Q44, `lem-sfb-fixed-hyperplane-restriction-cohomology`.
The item has a reviewed stage-1 split from Q40 but no Lean record. The maintenance
handoff in brief-stage2 section 0 explicitly permits stating such a node; this does
not reopen its proof split. The original statement and every proof step are preserved.
There is no released repair note for the item.

The module `Sheaf.AlgebraicGeometry.FixedHyperplaneRestrictionCohomology` states
`AlgebraicGeometry.ProjectiveSpace.fixed_hyperplane_restriction_cohomology` with
one `sorry`, as required in stage 2. Three real helper definitions merely specialize
existing maps: actual global sections of an i-map, the cohomology map of multiplication,
and the canonical cohomology restriction. Their data contain no `sorry`.

Hypotheses and conclusions are rendered as follows. Throughout, the Lean degree pair
`d, 1 + d` represents the source pair `D - 1, D`, via `D = 1 + d`; integer translation
is bijective, so negative twists and every integer degree are included.

| Node clause | Lean rendering |
| --- | --- |
| k is a field | `(k : Type u) [Field k]`, with no infinite-field assumption |
| n is at least one | `(n : ℕ) (hn : 1 ≤ n)` |
| X is projective n-space over k | `ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))`; the coordinate index has exactly n+1 elements and lies in the field's universe |
| E is a coherent O_X-module | `E : X.Modules` and `hE : RingedSpace.IsCoherent X.toRingedSpace E` |
| s is a nonzero global section of O_X(1) | `s : Γ(twist ... 1, ⊤)` and `hs : s ≠ 0` |
| i is the closed immersion of the zero scheme of s | `i : H ⟶ X`, `[IsClosedImmersion i]`, and `hH : i.ker = Scheme.Modules.Hom.zeroLocus (Scheme.Modules.homOfGlobalSection _ s)`; a closed immersion with this ideal is exactly the specified closed subscheme, up to its canonical isomorphism |
| G is i^*E | `(Scheme.Modules.tensorPullback i).obj E`; no independent G or isomorphism is assumed |
| G(d) is G tensor i^*O_X(d) | The explicit `MonoidalCategoryStruct.tensorObj (C := H.Modules)` in the edge-map term has exactly these factors; it is the target of `regularHyperplaneRestriction` |
| G is coherent | `hG : RingedSpace.IsCoherent H.toRingedSpace ((Scheme.Modules.tensorPullback i).obj E)` |
| s acts injectively in every twist | `hinj : ∀ d : ℤ, Mono (regularHyperplaneMultiplication k n E d s)`; in the sheaf category, Mono means sheaf injectivity, not surjectivity/injectivity of all sections in place of exactness |
| The canonical sheaf sequence is short exact | For every d, the theorem supplies `w` and `hS : (ShortComplex.mk ... w).ShortExact`; its arrows are the existing multiplication and `regularHyperplaneRestriction i E (twist ... (1+d))` |
| Pushforward uses sections on inverse-image opens and induced scalar action | Exactly `Scheme.Modules.pushforward i`, as used by the existing restriction map; no replacement direct image |
| The specified cohomology edge map is an isomorphism for every q | `∀ q : ℕ, ∃ he : IsIso (Scheme.Modules.moduleCohomologyEdgeMap i G(1+d) q), ...` |
| The cohomology sequence starts with zero then H^0(E(d)) | `Function.Injective (fixedHyperplaneCohomologyMultiplication k n E d s 0)` |
| Exactness at H^q(E(1+d)) | First `Function.Exact`, from the cohomology multiplication map to `fixedHyperplaneCohomologyRestriction ... (1+d) q` |
| Exactness at H^q(H,G(1+d)) | Second `Function.Exact`, from that restriction to `regularHyperplaneConnecting ... w hS q he` |
| Exactness at H^(q+1)(E(d)) | Third `Function.Exact`, from that same connecting map to multiplication in degree q+1; this ensures the entire long exact sequence, not just two positions |
| Boundary is that of the associated short exact sequence | `regularHyperplaneConnecting` is inverse of the specified edge followed by `RingedSpace.moduleCohomologyBoundary` of precisely `w,hS`; no arbitrary boundary is existentially chosen |
| Maps to H are canonical restriction | `fixedHyperplaneCohomologyRestriction` is definitionally `moduleCohomologyFMap i` applied to the normalized-unit/tensor-comparison restriction map |
| Restriction of linear sections is onto | `Function.Surjective (fixedHyperplaneGlobalSectionsMap i ((tensorPullbackSectionAdjunction i).unit.app (twist ... 1)))` |
| r_(d+1)(uv) = r_d(u)(v restricted to H) for all u,v | The final universally quantified equality applies the actual section map to `(regularHyperplaneMultiplication ... v).app ⊤ u`; its right side applies `regularHyperplaneRestrictedMultiplication ... v` to the actual restriction of u. That map is tensor pullback of ambient multiplication through the canonical tensor comparison, so is precisely multiplication by the restricted v, with frame formula `(m,c) ↦ cm`. The order `1+d` is the canonical twistMulHom order. |

All cohomology is the recorded `RingedSpace.moduleCohomology`, derived global sections
of module sheaves. Forgetting scalars to `AddCommGrpCat.{u}` allows comparison of the
ambient and hyperplane coefficient rings without changing the groups or exactness.
The degree-zero cohomology restriction identifies with the actual section map through
the existing degree-zero property of `moduleCohomologyFMap`; the section clause uses the
actual map directly, not an unspecified isomorphism.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs; `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.
- `ProjectiveSpace.twist`, WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist,
  together with canonical `twistMulHom` and `twistTensorIso` used by the existing helpers.
- `RingedSpace.IsCoherent`, WeilConjectures.AlgebraicGeometry.Coherent; Mathlib's
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType` are the other
  notions of the same dependency node. The live shared record is retained; see the R2 repair below.
- `Scheme.Modules.Hom.zeroLocus`, WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus,
  applied to `homOfGlobalSection _ s` between invertible modules.
- `Scheme.Modules.tensorPullback` and `tensorPullbackSectionAdjunction`,
  Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction; the unit is fixed by
  the section formula `m ↦ 1 tensor m`.
- `sheafCohomologyAndHigherDirectImages`, WeilConjectures.AlgebraicGeometry.PQFCohomology;
  its established degree functors are `RingedSpace.moduleCohomology`.
- `Scheme.Modules.moduleCohomologyFMap` and `moduleCohomologyEdgeMap`,
  WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap.
- `regularHyperplaneMultiplication`, `regularHyperplaneRestriction`,
  `regularHyperplaneRestrictedMultiplication`, `regularHyperplaneConnecting`,
  Sheaf.AlgebraicGeometry.CoherentRegularHyperplaneRestriction. The new existing
  definition owner `def-sfb-regular-hyperplane-restriction-maps` is added to stmt_deps
  solely for these canonical definitions; the finite-family existence theorem is not used.

All recorded proof-dependency modules that exist are imported privately, including the
closed-immersion quotient, affine edge isomorphism, pullback tensor comparison, full
long exact sequence, Noetherian/coherence equivalence, and FMap functoriality and
basic properties. The six source-based proof steps are included in the theorem docstring.
Sources read: Stacks varieties.tex labels lemma-hyperplane (089Z),
lemma-exact-sequence-induction (08A0), remark-exact-sequence-induction-cohomology (0EGK),
including the displayed coordinate calculation and exact sequence. The infinite-field
assumption is needed for selecting a section, not for the fixed-section consequences.

Edge cases checked before writing:

- n=1 is included: H is a point and H^1(P^1,O)=0 still proves the linear surjectivity.
- Finite fields are included; the fixed regular section replaces any avoidance argument.
- E=0 is included, with trivial short/long sequences and product identity.
- Modules supported away from H give G=0, still satisfying the statement.
- A nonzero module supported on H with s acting by zero fails hinj, as it should.
- All negative twists and d=0 are included. q=0 gives the complete initial segment;
  arbitrary q and the third exactness clause provide every remaining term.
- s=0 and n=0 are excluded by the actual source hypotheses, not by the encoding.
- H is not required to be a particular chosen representative of its closed subscheme;
  arbitrary closed immersions with the specified ideal are covered.
- The universe lift of the finite coordinate set changes no coordinates or field;
  arbitrary field universes are allowed. No extra derived-category size assumption is added.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “For a fixed nonzero regular section of O(1) on projective
  space the restriction sequence is short exact and gives the long exact cohomology
  sequence, with surjective restriction of linear sections and compatibility with products”.
  Eight hits: Profinite.NobelingProof.succ_exact; MayerVietorisSquare.shortComplex_shortExact
  and shortComplex_exact; group-cohomology exactness results; and projective-resolution
  exactness. None states this fixed-section result.
- `msearch.py ... loogle '"SheafOfModules", "ShortExact"'`: zero hits.
- `msearch.py ... grep 'hyperplane|regularHyperplane|restriction.*[Ss]hortExact'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` in WeilConjectures/AlgebraicGeometry and Sheaf/AlgebraicGeometry for hyperplane,
  Hyperplane, restriction/cohomology and twist multiplication found the landed
  finite-family existential infinite-field theorem and its useful helper definitions.
  That theorem does not state this universal fixed-section result over arbitrary fields.
- `rg` for the exact item id in both Lean roots: no hits. Search for the proposed
  fixedHyperplane names in both roots: no hits before creating this module.
- Read both the old IsQuasiCoherentFiniteType and the published IsCoherent definition;
  the former omits the defining kernel clause of coherence and the latter is exact.

No statement correction or STATEMENT-DISPUTED issue is needed. The R1 repair adds
a definition-ownership node for the four existing canonical maps.
The original natural-language statement, source, proof, and proof_deps are unchanged.

## New nodes

`def-sfb-regular-hyperplane-restriction-maps` records, with `existing: true`, the four
unchanged definitions `regularHyperplaneMultiplication`, `regularHyperplaneRestriction`,
`regularHyperplaneRestrictedMultiplication`, and `regularHyperplaneConnecting` in
`Sheaf.AlgebraicGeometry.CoherentRegularHyperplaneRestriction`. Its source is Stacks
08A0, local multiplication, and 0EGK, twisted restriction and cohomology sequences.
Its statement gives each actual construction: ambient multiplication by the section,
normalized adjunction unit followed by tensor comparison, conjugated tensor pullback
of multiplication, and inverse edge followed by the original connecting morphism.
The six statement dependencies are exactly those requested by R1. The main declaration
signature is copied verbatim. No Lean file is added or changed for this new node.

Searches run during repair: msearch LeanSearch with query “canonical twisted hyperplane
multiplication restriction map pullback tensor comparison connecting morphism cohomology
edge inverse” returned eight homological-complex/cotangent results, none an exact map.
LeanFinder with query “Multiplication on a twisted module by a section of O(1), canonical
restriction via pullback adjunction and tensor comparison, and edge-transported cohomology
boundary” returned eight unrelated group/nonabelian cohomology results. msearch grep of
the four exact names returned zero Mathlib hits. rg over the DAG and both Lean roots
found exactly the landed NR module and its theorem-node listing, with no definition
owner. blueprint_refs.py search hyperplane returned det-sp-tower-classes and
det-sp-zero-section-affine-space, neither a map-definition node. The ancestor command
returns None, matching the item's inherited blueprint.from.node; its via is copied
with this item prepended. Searches are also recorded in the new node.

## Returned-delivery repairs

R1 (H2): replaced the statement dependency on the finite-family theorem with the new
existing-definition owner above. Read all four source signatures and bodies again:
none chooses data from the existence theorem. The general restriction applies to any
scheme morphism and any two modules; the boundary requires the specified short exact
sequence and invertibility of its canonical edge; the specialized multiplications
allow every field, n=0, all integer twists and the zero section. The definition node
preserves this generality. It makes no claim of short exactness for arbitrary sections.

R2 (H2/H13): restored `pqf-def-coherent.json` byte-for-byte from the live shared clone,
including Q25's complete landed lean record. The item continues to use the full
`RingedSpace.IsCoherent` from `WeilConjectures.AlgebraicGeometry.Coherent`, whose kernel
clause was reread. Its lean.note explains this exactly as the NR sibling does: on the
locally Noetherian projective spaces at issue it agrees with quasi-coherence plus finite
type by pqf-lem-coherent-ft-locnoeth, while the shared dependency record is not rebound.
There is no dependency-module repair in this packet.

The returned immutable head was 591fbf28f16c; its saved packet was retained and its
initial dry run passed as 35d5f810f9a. These repairs change only DAG metadata and this
report. The Lean source remains byte-identical to the retained packet. The delivery
wrapper refreshes/rebases against current main. The reviewer explicitly requested no
separate compile because no Lean file changes; the prescribed dry run performs its
normal compile and existing-declaration checks.

## Second reading by Q44

This is a second pass in the same worker session; independent review is performed by
the maintainer on delivery, as required by the dispatch brief. No sub-agent was started.
I reopened the item and module and checked each binder and conjunct against the table.
In particular, checked that hH specifies the scheme-theoretic ideal, hG concerns the
actual pullback, and hinj is a hypothesis for every integer degree, with no infinite-field
restriction hidden in a helper. The helper definitions have no such assumption.

The full long exact sequence needs the third position (boundary followed by multiplication)
and the initial injection in addition to the two positions in the neighboring finite-family
module. Both are present in this statement. The boundary uses the same w,hS and edge
inverse as the associated short exact sequence. Linear-section surjectivity concerns the
unit on O(1), independent of E. The final equality quantifies over all u and v and uses
the actual section restriction, not an arbitrary cohomology-group isomorphism. Canonical
multiplication is reused rather than copied. The returned metadata mismatches are now
repaired as R1 and R2 above.
The new definition statement was checked against all four unchanged bodies, and Q25's
record was compared byte-for-byte. No mathematical item statement was changed.

Validation: scompile.py compiled this module in both sandbox and library modes without
errors or warnings (2.9 seconds each on the initial run). The final delivery dry run also
checks the unchanged item module and all four declarations of the new existing definition node.

Repair validation: the first repaired dry run requested the schema field `import_flags`
on the new definition node; added the empty list and reran the prescribed dry run.

The repaired packet passed preflight and all wrapper compilation checks in dry run
55dbcd56660. Final self-check: the item changes only lean and stmt_deps; all six
citations of the new node match its dependencies, its main signature is verbatim,
and the restored shared coherence node is omitted from the staged delta.
