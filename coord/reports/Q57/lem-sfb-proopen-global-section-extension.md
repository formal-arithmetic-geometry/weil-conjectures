## Worker report

The module `Sheaf.AlgebraicGeometry.ProopenGlobalSectionExtension` states
`AlgebraicGeometry.proopen_global_section_extension`, with its entire proof
postponed by `sorry`. It introduces no definitions, helper axioms or new nodes.
Only the item's `lean` field changes. The declaration's docstring contains all
six proof steps from the node, including the empty-image case and the
constructible-avoidance argument.

Source checked: Raynaud, *Un critère d'effectivité de descente*, Propositions
1.1, 1.2(i) and 2.3(i), printed pp. 1–2 and 4–5, in the
[primary Numdam scan](https://www.numdam.org/article/SAC_1967-1968__2__A5_0.pdf).
Proposition 1.2(i) identifies the source with the induced ringed subspace;
2.3(i), applied to its whole quasi-compact space, gives the extension. No
finite-presentation or Noetherian assumption occurs. The source's local
representatives, compact overlaps, agreement neighbourhoods and gluing match
the six-step proof already present in this node.

Hypothesis and conclusion correspondence:

- Schemes Z and Y: `{Z Y : Scheme.{u}}`; their morphism: `(j : Z ⟶ Y)`.
  The universe `u` is explicit and arbitrary, and `autoImplicit` is not used.
- Quasi-compact morphism: `[QuasiCompact j]`, using Mathlib's inverse-image
  compactness condition, equivalent to the affine-open condition in the node.
- Flat morphism: `[Flat j]`, the recorded dependency's class. Its stalkwise
  interpretation is `Flat.iff_flat_stalkMap`.
- Monomorphism: `[Mono j]`, precisely cancellation of postcomposition by j
  on morphisms from every test scheme in the category.
- Quasi-compact Z: `[CompactSpace Z]`. This is topological compactness without
  a Hausdorff requirement, hence the stated finite-subcover property.
- Quasi-separated Y: `[QuasiSeparatedSpace Y]`. The equivalence
  `quasiSeparatedSpace_iff_forall_affineOpens` identifies it with compactness
  of intersections of affine opens, exactly the node's convention.
- E is `Set.range j`. The first conjunct
  `StableUnderGeneralization (Set.range j)` expands to closure under points
  y specializing to an image point e. In Mathlib's convention, `y ⤳ e`
  means `e ∈ closure {y}`; the direction is therefore the one in the node.
- Every global function: `∀ s : Γ(Z, ⊤)`. There is no condition on s.
- Open subscheme V of Y: `∃ V : Y.Opens` and the canonical scheme
  `V.toScheme`, whose inclusion `V.ι` is an open immersion.
- Quasi-compact V: `IsCompact (V : Set Y)`, equivalently compactness of its
  subspace and hence of the underlying space of `V.toScheme`.
- Contains E: `Set.range j ⊆ (V : Set Y)`.
- Factorization through the open: `∃ jV : Z ⟶ V.toScheme` with
  `jV ≫ V.ι = j`. Since `V.ι` is a monomorphism, this equation specifies
  the unique factorization from the node. The existential does not replace
  the canonical factorization by an unconstrained map.
- Extension t: `∃ t : Γ(V.toScheme, ⊤)` and `jV.appTop t = s`.
  `Scheme.Hom.appTop` is exactly pullback of global regular functions.
- No finite-presentation, Noetherian, nonempty or affine hypotheses are added;
  no uniform open for all s or uniqueness of the extension t is asserted.

Statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`, with `Flat.iff_flat_stalkMap` for interpretation.
- `def-weil-pbc-scheme-conventions` has a convention-only record and no
  declaration to import. Its compactness and separation conventions are
  the existing classes from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`. The open-subscheme data and inclusion
  use `Scheme.Opens.toScheme` and `Scheme.Opens.ι` from
  `Mathlib.AlgebraicGeometry.Restrict`. Global section pullback is the
  existing `Scheme.Hom.appTop` from `Mathlib.AlgebraicGeometry.Scheme`.

The four statement-dependency records are usable without repair. They are
public imports, together with the modules supplying the notation and classes.
Proof-only imports include the recorded modules
`WeilConjectures.Topology.PresheafModuleStalkFunctor`
(`PresheafOfModules.moduleStalkFunctor`),
`WeilConjectures.Topology.InverseImageStalk`
(`TopCat.Sheaf.exists_inverseImage_stalk_iso_commRing`),
`WeilConjectures.Topology.ProconstructibleClosureSpecialization`
(`Topology.exists_mem_iInter_closure_singleton`) and
`Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection`
(`AlgebraicGeometry.compactSpace_inter_of_quasiSeparated`). Mathlib's
`AffineScheme`, `Properties`, `Topology.Constructible`,
`Topology.Spectral.Basic`, `OpenImmersion` and
`Geometry.RingedSpace.LocallyRingedSpace` supply the other stated proof
interfaces. `lem-sfb-qc-flat-monomorphism-ringed-image` has no recorded
module or Mathlib match at the time of writing, so there is no proof-only
import to add for it; the proof docstring names the node. It is not needed
to type the present statement. No import cycle is introduced.

Edge cases checked before writing:

- If Z is empty, its image is empty and generalization stability is vacuous.
  V can be the empty open. Its ring of sections and that of Z are trivial,
  so the unique section pulls back to the only possible s. No binder
  excludes this case. In particular Y may also be empty.
- For an isomorphism j, Y is quasi-compact by the source hypothesis; take
  V to be the whole target and pull s across the inverse.
- For the generic-point inclusion `Spec Frac(A) → Spec A` of a domain, a
  section a/b extends on D(b). Thus the statement allows flat monomorphisms
  which need not have finite presentation or open image.
- The zero section is included; it may extend as zero on any suitable
  quasi-compact open neighbourhood. No invertibility condition is imposed.
- Y is allowed to be non-quasi-compact and non-Noetherian. Quasi-compactness
  is asserted only for Z, j, and the resulting open V.
- The factorization equation uses categorical order `jV ≫ V.ι = j`;
  `jV.appTop` consequently has the required domain Γ(V,O_V) and codomain
  Γ(Z,O_Z). It has no dependent transport or hidden `let` in its statement.

Searches for an existing statement (prescribed msearch.py wrapper, group Q57,
item `lem-sfb-proopen-global-section-extension`; raw wrapper records are in
sandbox `searches.jsonl`):

- LeanFinder: "A global regular function on a quasi-compact flat
  monomorphism into a quasi-separated scheme extends to a quasi-compact
  open neighbourhood of its image". Eight hits, headed by
  `exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated` and
  `exists_of_res_eq_of_qcqs`: these concern principal-open localization,
  not an arbitrary flat monomorphism. No exact statement.
- Loogle: `"Flat", "Mono"`. Twelve hits, including
  `IsOpenImmersion.of_flat_of_mono`, whose additional
  `LocallyOfFinitePresentation` assumption rules it out as a match.
- Mathlib grep: `(flat.*mono|mono.*flat|pro.?open|section.*neigh|neigh.*section)`
  in AlgebraicGeometry. Fifteen hits, including `Morphisms/FlatMono.lean`
  and flat pushout-section lemmas. None gives the extension assertion.
- LeanSearch: "Global sections of a quasi-compact pro-open subscheme extend
  to open neighbourhoods". Eight hits, including
  `Scheme.Opens.toScheme_presheaf_obj`, `isCompact_basicOpen` and
  `IsOpenImmersion.ΓIsoTop`; none covers an arbitrary quasi-compact flat
  monomorphism.
- Direct ripgrep in both `lean/WeilConjectures` and `lean/Sheaf` for
  `lem-sfb-proopen-global-section-extension` returned no match. Broader
  `proopen`, `proOpen`, flat-monomorphism/global-section and neighbourhood
  patterns found unrelated pro-etale restriction functors, flat-descent
  results and scalar-extension lemmas, with no matching statement.
- Candidate signatures read in Mathlib:
  `exists_of_res_eq_of_qcqs` compares functions on a principal open;
  `exists_appTop_π_eq_of_isAffine_of_isLimit` assumes an affine limit
  presentation; `Flat.generalizingMap` proves only the first clause.
  None states both conclusions under exactly these hypotheses.

No statement fault or mathematical dispute was found. No statement correction,
dependency module or new definition node is needed.

## Second reading by Q57

Final rereading by the dispatched worker, without starting another agent as
instructed by the dispatcher. The maintainer supplies the independent review.
I reopened the node and the actual module signature and checked both conjuncts:
image generalization stability has the correct specialization direction, and
extension is quantified over every global section separately. The six input
objects/conditions are the two schemes, j, its three morphism properties,
compact source and quasi-separated target. The existential includes an actual
open, compactness, image containment, a morphism whose composition is j, and
a section with the precise pullback equality. The factorization equation is
necessary to connect the extension map to j. There are no additional
hypotheses, section restrictions or uniqueness assertions. Empty schemes and
non-finitely-presented monomorphisms remain allowed. No mismatch was found
and no node field other than `lean` was changed. All statement variables and
the universe are explicitly bound. The theorem has exactly one `sorry` and
no definition carries postponed data.
