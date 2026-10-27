## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceSecondAdicTorsionTransfer` states
`AlgebraicGeometry.AlgebraicSpace.secondAdic_torsion_transfer`, with proof `sorry`.
The original node statement, proof, and proof dependencies are unchanged. The only
added statement dependency is the new definition node described below. All work is
in the assigned sandbox; all three files compiled through scompile.py against the
published server library, individually, without errors or unexpected warnings.
No statement correction or STATEMENT-DISPUTED issue was found.

Clause-by-clause correspondence:

- Scheme S and algebraic space X: `{S : Scheme.{u}} (X : AlgebraicSpace S)`.
  The explicit universe u is shared with the schemes and rings of the existing site;
  the site/category object and morphism universes are inherited, with no imposed equality.
- Noetherian X: `hln` asserts IsLocallyNoetherian for every etale scheme chart,
  `hqc` is CompactSpace on the point space, and `hqs` is IsAbsolutelyQuasiSeparated.
  These are exactly the three conditions in the recorded adic-system definition.
- Commutative Noetherian A: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- The specified Spec A → S is `b`, and the S-map X → Spec A is
  `f : X ⟶ schemeSpace (Over.mk b)`. The hypotheses `hsep` and `hft`
  render separatedness and finite type using the dependency's map predicates.
- J and K: `(J K : QuasiCoherentIdeal X)`, using the existing subobjects of O_X.
- The closed thickening X_q^K and its completion equivalence: `hcompletion` quantifies
  over every q with `1 ≤ q` and asserts `SupportedKilledAdicCompletionEquivalence f J K q`.
  This uses exactly the ambient full-subcategory identifications in the first paragraph
  of the proof of Stacks 08BC (spaces-more-morphisms.tex, after lemma-existence-tricky).
  A coherent module on X_q^K is a coherent module on X killed by K^q; a coherent
  adic system there is an ambient one killed termwise by K^q. Proper support is preserved.
  The definition retains the ACTUAL quotient-diagram completion on objects and arrows,
  its landing in the target subcategory, hom-set bijectivity, and essential surjectivity.
  Consequently this is the source's precise equivalence condition on the indicated full
  subcategories. It is not just faithfulness, exactness, or an unspecified equivalence.
  No ideal power, closed subspace, or pullback ideal has been replaced by an arbitrary map.
- `M : CoherentAdicSystem X J hln hqc hqs` and the analogous K-adic N use
  the recorded full subcategories. `H`, `hHqc`, `hHcoh` give the coherent module H
  with its quasi-coherence and RingedSpace.IsCoherent on every etale scheme restriction.
- Proper support of M and N: `hMproper` and `hNproper` apply
  CoherentAdicHasProperSupportOver to their diagrams, hence to their first terms.
  `hHproper` applies it to the constant H diagram. In each case this is the
  recorded proper closed carrier `i : Z → X`, `MapIsProper (i ≫ f)`, and finite type
  quasi-coherent Q with `i_*Q ≅` the specified module; no support-set replacement.
- Maps a and d: natural transformations to the corresponding
  `coherentAdicCompletionDiagram` applied to H. Their components therefore have exactly
  the ordinary quotient targets H/J^nH and H/K^eH and commute with transitions.
- The isomorphism of double diagrams σ: an iso from
  `N.obj ⋙ coherentAdicCompletionDiagram J` to the flip of
  `M.obj ⋙ coherentAdicCompletionDiagram K`. Thus its (e,n) component has the direction
  N_e/J^n N_e → M_n/K^e M_n and is natural in both variables, not merely a family of isos.
- The quotient interchange θ: an iso between the same two iterated quotient diagrams
  for H, with `hθ` saying its composite with H → H/K^eH → (H/K^eH)/J^n is precisely
  H → H/J^nH → (H/J^nH)/K^e. The quotient universal properties determine this iso
  uniquely. Making θ a bound variable with this defining equation does not add a
  mathematical restriction: both iterated cokernels represent maps killing J^nH and K^eH.
- Compatibility is `hcompat`: σ followed by the K^e reduction of a_n equals the
  J^n reduction of d_e followed by θ, using the actual completion functor's map.
- Positive t: `(t : ℕ) (ht : 1 ≤ t)`.
- The K^t hypothesis is `ha`, for EVERY component n, and quantifies over every
  ordinary KernelFork with IsLimit and CokernelCofork with IsColimit. These are in
  X.Modules, not Coh(X,J). `AdicPowerKills K t` is the existing local ideal-product
  annihilation condition. This is the same universal-property encoding as the recorded
  CoherentAdicKernelCokernelKilled, with the particular supplied exponent retained.
- Conclusion: for every e the ordinary kernel and cokernel of `d.app (op e)` are killed
  by `AdicPowerKills K (4 * t)`. No existence of a new system, map, or algebraization
  is asserted. The stronger 2t bound in the natural-language proof is not the conclusion.
- Positive level convention: `op n` means n+1 throughout, including n=0 and e=0
  for the first positive levels. There is no zeroth adic term or excluded first level.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Spec, Spec.map.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  its EtaleSite, etaleForget, structureSheaf, Modules, and IsRepresentableWith.
- Sheaf.AlgebraicGeometry.SpaceCoherentAdicSystem: adicQuotientModel with its full
  projection-normalized universal property, coherentAdicCompletionDiagram,
  IsCoherentAdicSystem, CoherentAdicSystem, AdicPowerKills. This module is imported
  publicly and retains all fourteen original declarations unchanged; its sole addition is
  the proper-support generalization described below.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh is the full
  subcategory for Mathlib SheafOfModules.IsQuasicoherent, used in the imported notions.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: moduleDirectImage and its
  ModuleDirectImageModel, chart projections and limit universal property.
- Sheaf.AlgebraicGeometry.CoherentFiniteType publicly exposes the recorded
  WeilConjectures.AlgebraicGeometry.Coherent: RingedSpace.IsCoherent.
- Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsSeparated,
  MapIsFiniteType, MapIsProper.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion, on scheme tests.
- Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor: ProperQuotient.properSupport
  supplies the proper closed-carrier convention used verbatim in the repair interface.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction: schemeRestriction,
  as used by the recorded coherence and adic-system interfaces.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated:
  IsAbsolutelyQuasiSeparated. The size-convention node is metatheoretic and has
  no declaration; explicit universe polymorphism renders it.

Proof dependency imports: AlgebraicSpaceAffineChartCalculus and the upstream
KernelCokernelAnnihilatedModIdeal, whose module-only result does not state this item.
The other proof-only nodes have no Lean record in the current DAG:
lem-sfb-space-noetherian-coherent-support, lem-sfb-space-noetherian-coherent-acc,
lem-sfb-space-proper-support-closed-operations,
lem-sfb-space-module-proper-carrier-support, lem-sfb-space-closed-adic-dictionary.
They are retained as proof dependencies and in the complete proof docstring; no missing
proof dependency is assumed as a new hypothesis. In particular the source's ambient
subcategory encoding is spelled out in full instead of depending on a not-yet-stated
closed-adic-dictionary interface.

Edge cases checked against the definitions: empty X; H=0 and zero adic systems;
J=0 (completion is the constant diagram); J=O_X (the completion-equivalence hypothesis
forces the relevant subcategory to vanish); K=0 (all positive K-powers vanish);
K=O_X (the killed subcategories are zero, and the annihilation conclusion is automatic);
n=e=0 mean positive first levels; t=1 gives 4; no t=0 case is silently allowed.
For the new definition q=0 uses K^0 H=H and thus the zero supported subcategory.
The faithful-completion hypothesis is material: on k[x] with J=(x), the module
k[x]/(x-1) has zero completion but is nonzero, so it cannot simply be dropped.

Searches performed through msearch.py (also logged in searches.jsonl):

- LeanFinder: “Transfer uniform ideal-power torsion bounds on ordinary sheaf kernels
  and cokernels through two coherent adic quotient diagrams”. Eight hits, on ordinary
  module completion/quotient and local-cohomology diagrams; no exact space result.
- Loogle: `AdicCompletion, LinearMap.ker`. Three completion-evaluation kernel lemmas;
  no coherent algebraic-space double-diagram transfer theorem.
- Mathlib grep: `adic.*torsion|torsion.*adic|double.*quotient`. Twelve unrelated
  double-coset, preradical, valuation and Witt-vector hits; no match.
- LeanSearch: “The adic completion functor on coherent sheaves with proper support
  killed by a fixed ideal power is fully faithful and essentially surjective”.
  Module AdicCompletion and ordinary exactness results; no supported space functor.
- LeanFinder: the closed-thickening ambient-subcategory formulation. Eight module
  adic completion hits; no exact interface.
- Loogle: `CategoryTheory.Functor.IsEquivalence`. The generic equivalence criterion
  is full, faithful and essentially surjective; it provides no specific restricted
  functor or the supported/killed object predicates.
- Mathlib grep `completion.*(proper|coherent)|proper.*completion` in AlgebraicGeometry:
  zero hits. CategoryTheory grep for supported completion/essential surjectivity:
  three unrelated preradical/reflexive-pair hits.
- rg of WeilConjectures and Sheaf for second-adic/double quotient/completion and proper
  support found existing SCHEME-only GrothendieckDevissageSecondAdicSystemTorsion
  and its kernel/cokernel modules. Those concern scheme Zariski modules, so do not
  state this algebraic-space small-etale assertion. The exact item-id search upstream
  found no match. New declaration-name searches found no duplicates.
- DAG definition search and `tools/blueprint_refs.py search supported adic completion`
  found no existing definition (zero blueprint matches). The existing closed-adic
  dictionary is a theorem about transport, not this named restriction predicate.
  The inherited ancestor is null (confirmed by blueprint_refs.py ancestor); the
  new node retains the inherited via chain and names the current latest-blueprint
  direct-image proof paragraph (3). The Stacks source was read directly, including
  both quotient-subcategory identifications and the omitted 2t/4t estimates.

## Dependency modules

`def-sfb-space-coherent-adic-system`: repaired by the maintainer's option (a).
The delivered SpaceCoherentAdicSystem.lean is the current live module with the single
predicate CoherentAdicHasProperSupportOver appended. All fourteen live declarations,
their signatures, docstrings and bodies are preserved byte-for-byte. The node record
retains the module SpaceCoherentAdicSystem, headline CoherentAdicSystem and all fourteen
live names, and appends the new name. The statement field is the unchanged headline's
verbatim multiline signature from the source. The former separate
SpaceCoherentAdicProperSupportOver module has been removed from this packet.

The original CoherentAdicHasProperSupport requires ambient S to be Spec A; the appended
predicate exposes the same proper closed-carrier formula for any specified structural
map over S. It also handles module support via the constant diagram. Its declaration
name is AlgebraicGeometry.AlgebraicSpace.CoherentAdicHasProperSupportOver, the same
canonical name named in the Q72 parent return. Owning it in SpaceCoherentAdicSystem
avoids competing definitions in distinct support modules. The new supported-killed
module now imports this canonical owning module directly. No mathematical statement,
completion construction, quotient model or existing support predicate was altered.

## New nodes

`def-sfb-space-supported-killed-adic-completion` defines the full subcategory of coherent
proper-support modules killed by K^q, the full subcategory of coherent proper-support
J-adic systems killed termwise by K^q, and the condition that the specified canonical
completion restricts to an equivalence between them. All three are real Prop definitions.
The equivalence condition gives the image condition, hom bijectivity and essential
surjectivity using the existing quotient-diagram functor. Source: Stacks 08BC, first
paragraph of the proof, which explicitly uses these ambient full subcategories for
modules and adic systems on the closed thickening. The three kinds of semantic/type/
source search above found no such algebraic-space restriction interface; the new node
records the actual search output, and the item cites it. No postponed helper theorem
or construction with sorry data was introduced.

## Returned delivery repair

The immutable returned head was 7fe1e0242930. The sole H13/H2 defect was replacing
Q67's complete dependency binding with a binding for only the new proper-support
predicate. This packet follows option (a) of the return: extend the live owning source,
preserve its headline and all fourteen recorded names, and add the fifteenth name.
The old support-only module is deleted from the packet and its consumer import is
redirected to SpaceCoherentAdicSystem. The theorem module, its signature, the three
supported-killed definitions, and the new node's mathematical statement are unchanged.
The report's dependency description now reflects the actual preserved interface.
The H4 naming point is resolved by using the exact CoherentAdicHasProperSupportOver
name prescribed for Q72, in the common owning module. The canonical predicate is the
same proper-carrier formula already accepted by both independent return reviews.

Compared against the current read-only main source, the updated owning module is
exactly that source followed by the new definition (before the namespace end).
The delivery wrapper rebases this repaired packet on current main for validation.

Repair validation: the required scompile.py invocation compiled the extended canonical
SpaceCoherentAdicSystem module, SpaceSupportedKilledAdicCompletion, and the actual
SpaceSecondAdicTorsionTransfer consumer separately against the published live build.
All passed with no errors or unexpected warnings. A source comparison additionally
checked that the original source prefix is unchanged, all fourteen original recorded
names occur in order before the new fifteenth name, the module/headline are preserved,
and the dependency JSON differs from current main only in its lean field.

## Second reading by Q158

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
