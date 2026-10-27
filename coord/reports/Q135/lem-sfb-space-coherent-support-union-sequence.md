## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentSupportUnionSequence` states
`AlgebraicGeometry.AlgebraicSpace.exists_coherent_subobject_of_support_union`, with its
whole proof `sorry`. No definition, helper theorem, or proof is added. The source is
Stacks, Spaces Cohomology, Tag 07UP, `lemma-prepare-filter-support`, read in
`literature/stacks-project/spaces-cohomology.tex:2218`: its Zprime is T₁ and Z is T₂.
The node's mathematical statement is unchanged.

Clause-by-clause rendering:

- Scheme S and algebraic space X over S: `{S : Scheme.{u}} (X : AlgebraicSpace S)`.
  These use the recorded `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.AlgebraicSpace`.
- Local Noetherianity on all etale scheme charts: `hln : ∀ T : X.EtaleSite,
  IsLocallyNoetherian (X.etaleForget.obj T)`. No chosen atlas or finite-type restriction
  is imposed on the charts.
- Quasi-compactness: `hqc : CompactSpace (Point X.obj.obj)`, for the existing final atlas
  topology. This is ordinary quasi-compactness; no Hausdorffness is required.
- Quasi-separatedness: `hqs : IsAbsolutelyQuasiSeparated X`. Its existing definition
  tests compactness of the sheaf fibre products of every pair of affine scheme maps
  to X (Stacks 0AHR). It is absolute, including for a non-quasi-separated base S.
- Module on the original small etale ringed site: `F : X.Modules`.
- Coherence of F: `hFqc : F.IsQuasicoherent` and `hFcoh : ∀ T : X.EtaleSite,
  RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
  ((X.schemeRestriction T).obj F)`. This is exactly the node's site quasi-coherence
  and chartwise coherence, including the finite-type-kernel condition of Tag 01BV.
- Closed subsets of the point space: `T₁ T₂ : Set (Point X.obj.obj)` with
  `hT₁ : IsClosed T₁` and `hT₂ : IsClosed T₂`.
- Exact support equality, not merely containment: `hSupp : moduleSupport F = T₁ ∪ T₂`.
  `moduleSupport` is the already landed nonzero-geometric-germ locus. No alternate
  ordinary-stalk support predicate is introduced.
- Submodule of F: `A : Subobject F`, whose canonical `A.arrow` is monic.
- Quotient B = F/A: `B : X.Modules`, `q : F ⟶ B`, `w : A.arrow ≫ q = 0`, and
  `Nonempty (IsColimit (CokernelCofork.ofπ q w))`. Thus B is the cokernel of the actual
  inclusion, determined with its quotient map by the universal property. B is not
  an unconstrained sheaf; there is no added hypothesis on the input. This form avoids
  asking for an additional global sheafification choice on the large chart category.
- Coherence of A and B: each has `SheafOfModules.IsQuasicoherent` and exactly the
  same universal chartwise `RingedSpace.IsCoherent` condition used for F.
- Exact sequence 0 → A → F → B → 0:
  `(ShortComplex.mk A.arrow q w).ShortExact`, Mathlib's exactness, mono and epi predicate.
  The cokernel condition also expresses the node's explicit quotient convention.
- Required support inclusions: `moduleSupport (A : X.Modules) ⊆ T₁` and
  `moduleSupport B ⊆ T₂`. No equality or extra vanishing condition is asserted.

The introductory definitions of reducedness, irreducibility and closed immersions do
not add hypotheses: no reducedness, irreducibility, or specified closed immersion is
assumed in this node. The proof chooses a reduced closed subspace as in Tag 07UP.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `EtaleSite`, `etaleForget`, `structureSheaf`, `Modules`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, the original
  `SheafOfModules.IsQuasicoherent`, and its required slice-instance interfaces.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes the recorded
  `RingedSpace.IsCoherent` (defined in `WeilConjectures.AlgebraicGeometry.Coherent`)
  and Mathlib's quasi-coherence and finite-type predicates. The conjunction
  `Scheme.Modules.IsQuasiCoherentFiniteType` is not substituted for coherence.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`;
  its `Point` and chart-point interfaces come from `AlgebraicSpacePointClasses`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  available for the proof's scheme-test closed immersion, not an additional binder.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport`: `moduleSupport`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- Mathlib's `Subobject`, `CokernelCofork`, `IsColimit`, `ShortComplex.ShortExact` are
  the actual categorical submodule, quotient and exactness notions.

The three landed definition nodes `def-sfb-space-module-support`,
`def-trf-space-module-scheme-restriction`, and `def-sfb-space-absolute-quasi-separated`
are added to stmt_deps for those interfaces, under brief-stage2 §5 (landed nodes may
be added). Their node records, definitions, signatures and docstrings were read.
No new node or dependency-record repair is needed.

Available proof dependencies are imported privately: `ReducedClosedSubspaceSupport`,
`AlgebraicSpaceIdealClosedSubspaceCorrespondence`, `AlgebraicSpaceCoherentSupportIdealPower`,
`AlgebraicSpaceEtaleOpenImage`, and `RingedSiteModules`. Their recorded declarations and
proof docstrings were read. `lem-sfb-noetherian-space-topology` and
`lem-sfb-space-integral-qcqs-permanence` have no Lean record locally, so there is no
module to import for them yet. They remain unchanged proof dependencies, and the
five-step docstring preserves their roles. No new statement prerequisite is missing.

Edge cases checked before writing: empty X; F = 0 (the support equality then forces
both closed sets empty); T₁ empty (A = 0, B = F); T₂ empty (A = F, B = 0); equal or
intersecting closed sets; disjoint supports; nonreduced X. The proof uses an arbitrary
natural ideal-power exponent, including n = 0. No characteristic, separation of the
base, nonzero-sheaf, nonempty-support, positive-exponent or finite-atlas assumption
has been added. One explicit universe u is the existing algebraic-space convention;
the point carrier remains Type (u+1), not artificially shrunk. `autoImplicit false`
is set and all theorem binders and universes are explicit.

Searches (2026-10-24):

- msearch leanfinder: “A coherent module on a Noetherian algebraic space whose support
  is the union of two closed sets has a coherent submodule supported in the first
  with quotient supported in the second”. Eight hits, headed by `Module.support_quotient`,
  `Module.support_of_exact`, scheme ideal-support sup/iSup/sSup results and
  `Module.isClosed_support`. None gives this algebraic-space existence result.
- msearch loogle: `"IsCoherent", "support"`: zero hits.
- msearch leansearch: “coherent sheaf support union of two closed subsets short exact
  sequence”. Eight hits: `Module.support_of_exact`, scheme ideal-support declarations,
  and the Mayer-Vietoris short exact sequence; no match.
- msearch grep: `coherent.*support.*union|support.union.*coherent|prepare.filter.support`
  in Mathlib/AlgebraicGeometry: zero hits.
- rg on lean/WeilConjectures and lean/Sheaf for `support.union|support_union|
  prepare.filter.support|lem-sfb-space-coherent-support-union-sequence`: found the
  scheme-only `WeilConjectures.AlgebraicGeometry.CoherentSupportUnionExactSequence`
  theorem, whose full signature was read. It takes a Scheme and ordinary stalk
  support and cannot apply to arbitrary algebraic spaces. Remaining hits are the
  consuming filtration proof docstrings and unrelated supported-torsion commentary.
- rg of algebraic-space modules for coherent, support, Noetherian, submodule and
  quotient interfaces located the landed support/restriction/absolute-qs definitions,
  the ideal-power theorem and coherent filtration. These are reused, not copied.
  The existing full declaration name `exists_coherent_subobject_of_support_union`
  did not occur in the project sources.

No statement dispute or source fault found. The mathematical statement and proof plan
are preserved; only lean and the three additional landed statement dependencies change.

## Second reading by Q135

This is the author's separate self-check, not an independent second worker: the
current dispatcher brief explicitly prohibits starting other agents; the maintainer's
independent review remains required. I reopened the node, Tag 07UP, dependency records,
and the completed module and matched every clause above. In particular the order is
A supported in T₁ and quotient B supported in T₂, corresponding to Zprime = T₁,
Z = T₂; coherence uses both quasi-coherence and the full chartwise coherence condition;
absolute quasi-separatedness is not replaced by quasi-separatedness over S; support
uses the landed definition; and the quotient universal property fixes B and q rather
than merely postulating a sheaf with a convenient support. The zero cases require no
extra nonemptiness assumption. Every theorem proof is sorry, no definition was added,
no private notation or local instance occurs, and every line is at most 100 characters.
No mismatch was found in this rereading and no statement correction was made.
