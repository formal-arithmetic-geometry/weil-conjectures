## Worker report

The module `Sheaf.Algebra.Homology.FiniteShortComplexAdicCohomologyLimit` states
`AdicCohomology.finite_short_complex_adic_cohomology_limit`, with `sorry` as its only
proof. No definitions or subsidiary theorems are introduced.

Read the item, both original statement dependencies, their recorded Mathlib
signatures and docstrings, the proof dependency, Stacks more-algebra.tex
`lemma-consequence-Artin-Rees` (Tag 0EGU), and the latest blueprint direct-images
proof (3) at the ancestor recorded in the node. The compact-object example module
is now withdrawn; its JSON still illustrates the record convention. No repair
note exists for this item.

Hypothesis and clause correspondence:

- A commutative Noetherian ring: `{R : Type u} [CommRing R]
  [IsNoetherianRing R]`. The universe is explicit and arbitrary.
- An arbitrary ideal: `(I : Ideal R)`, without properness, nonzero, or completeness
  assumptions.
- U -> V -> W with vu=0: `S : ShortComplex (ModuleCat.{u} R)`. Its fields X₁,
  X₂, X₃, f, g and zero give exactly these data.
- Finite terms: the three `Module.Finite R S.Xᵢ` arguments, separately and
  without requiring free, projective, or finite underlying sets.
- H=ker(v)/im(u): `S.homology`. Mathlib's `S.moduleCatHomologyIso` identifies
  this abstract module with its explicit kernel quotient by the range of
  `S.moduleCatToCycles`; this is precisely the image inside the kernel.
- The quotient complex at exponent n≥1: `S.map (AdicCohomology.quotient I
  (n+1))`, as used by `shortComplexTower`. The existing `quotient` functor
  actually quotients each term by `I^(n+1) • ⊤`, retaining R as scalar ring.
- Its cohomology and canonical transitions: `tower I S` is that short-complex
  tower followed by `ShortComplex.homologyFunctor`. Its transition morphisms
  are induced by `Submodule.factor` on the actual ideal-power inclusions.
- Right inverse limit as compatible sequences: `ModuleCat.sectionsSubmodule
  (tower I S)`. Its elements are families indexed by `ℕᵒᵖ` compatible with
  every tower morphism, with pointwise addition and R-action. No abstract
  categorical-limit identification is assumed.
- Left limit: `AdicCompletion I S.homology`, Mathlib's actual subtype of
  compatible families in H/I^nH. Mathlib includes n=0, where I^0H=H and
  the quotient is zero; omitting that forced zero coordinate gives precisely
  the node's positive-index compatible-sequence formula.
- A-linear isomorphism: `e S h₁ h₂ h₃ : AdicCompletion I S.homology ≃ₗ[R] ...`.
  The existential family specifies these isomorphisms simultaneously, allowing
  naturality to refer to both source and target comparison.
- Canonical maps on cycle classes: the first conjunct says for every completed
  x, every n, and every representative h of its residue at n+1, the n-th output
  coordinate equals `ShortComplex.homologyMap (S.mapNatTrans (projection I
  (n+1))) h`. This is the induced cycle-reduction map H -> H_n. The condition
  on h is exactly equality to the class modulo I^(n+1)H. Surjectivity of mkQ
  supplies such h for every x and n, so the formula determines all coordinates
  of the actual comparison; it imposes no density-only normalization and
  cannot admit an unrelated abstract equivalence.
- Naturality for ALL commuting triples: `f : S ⟶ T` is exactly a triple with
  the two commuting squares. The second conjunct quantifies over every finite
  target T, every such f, every completed x and every n. On the right-limit
  side it applies `homologyMap ((quotient I (n+1)).mapShortComplex.map f)`;
  on the left it applies `AdicCompletion.map I (homologyMap f).hom`. Equality
  at all n is equality of compatible sequences. Inverse naturality follows
  from this square and invertibility, with no additional conclusion required.

Dependencies used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (and its defining
  meaning `IsNoetherian R R`), recorded by def-weil-pbc-noetherian-ring.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, the FG top-submodule
  predicate, recorded by def-weil-finitely-generated-module.
- `Mathlib.RingTheory.Filtration`: `Ideal.exists_pow_inf_eq_pow_smul`, the
  mathlib_match of proof dependency lem-weil-pbc-artin-rees; imported privately
  as the stage-3 proof plan.
- `Sheaf.Algebra.Homology.AdicShortComplexCohomologyML`: `AdicCohomology.power`,
  `quotient`, `projection`, `shortComplexTower`, `tower`. The first three
  and the quotient transitions are owned by def-sf-adic-module-quotient-data.
  The two towers are owned by the new existing:true definition node
  def-sfb-adic-short-complex-quotient-tower. No conclusion of the
  Mittag-Leffler/constant-sheaf theorem is a statement dependency.
- `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`: `ShortComplex`,
  `homologyMap`, `moduleCatHomologyIso`, and `moduleCatCyclesIso` (the last
  two were read to verify the intended quotient interpretation).
- `Mathlib.Algebra.Category.ModuleCat.Limits`: `ModuleCat.sectionsSubmodule`.
- `Mathlib.RingTheory.AdicCompletion.Functoriality`: `AdicCompletion`,
  `AdicCompletion.eval`, `AdicCompletion.map`.

Edge cases checked mathematically before drafting: I=0 gives the original
cohomology and identity transitions at positive levels; I=R makes both limits
zero; zero terms and zero differentials are allowed; no exactness of the short
complex is assumed. For U=0 and v=p on V=W=ℤ, H=0 but each positive-level
H_n is a nonzero kernel, with zero adjacent transitions; its limit is zero,
consistent with the theorem. This checks that the claim is about the limit,
not a false levelwise isomorphism. The naturality clause permits all triples,
including zero maps and identity morphisms. There is no empty indexing-set
case because the stated index set is the positive integers.

Searches made (2026-10-24):

- msearch.py leanfinder: "The inverse limit of homology of ideal power quotients
  of a finite short complex is naturally the adic completion of its homology".
  Eight completion-related hits, including AdicCompletion, of, eval, and map
  infrastructure; none states the comparison theorem.
- msearch.py loogle: `"AdicCompletion", "homology"`: zero hits.
- msearch.py grep in RingTheory/AdicCompletion:
  `(homology|cohomology).*(AdicCompletion|completion)|(AdicCompletion|completion).*(homology|cohomology)`:
  zero hits.
- msearch.py leansearch: "The adic completion of the homology of a finite short
  complex of modules is the inverse limit of the homology of its quotients".
  Eight hits: completion definitions and ShortComplex module homology data,
  but no theorem identifying the two limits.
- rg of the project Sheaf and WeilConjectures trees for adic/completion with
  homology/cohomology found the reusable AdicShortComplexCohomologyML and
  PerfectTensorRoosCompletion modules, plus unrelated geometric comparison
  results. Read the full former module. The latter concerns perfect-complex
  tensor/Roos completion, not this arbitrary finite short-complex theorem.
- grep -rn for the exact item id under WeilConjectures: no hits.
- Focused rg under WeilConjectures/Algebra and Sheaf/Algebra for AdicCompletion
  with homology/cohomology: no equivalent comparison theorem.

No disputed statement, source correction, dependency-interface repair, or
hollow definition. The repair adds one ownership-only definition node. The theorem docstring reproduces all six proof steps: cycle
quotients, the two Artin-Rees bounds, shifted map and its independence,
transition/composite identities, compatible-sequence inverse, and naturality.

Validation: scompile.py compiled both the sandbox and intended library module
successfully, with no errors or unexpected warnings.

## Second reading by Q53

This is the dispatcher's sole worker's separate rereading; no second agent was
started, as explicitly instructed. Independent maintainer review is still the
next stage. Reopened the node, the complete statement file and the recorded
source declarations. Checked that the three finiteness hypotheses are retained,
that ShortComplex.zero is only the composition-zero assumption, and that both
limits are compatible-sequence modules. Checked carefully that the component
condition applies to every completed element and to every residue representative,
so it specifies the canonical comparison on the entire completion. Checked that
naturality uses the actual termwise quotient of the morphism, not an arbitrary
linear map between its cohomology groups. The simultaneous existential family
is equivalent to the canonical natural family because the component formula
uniquely determines each map. The apparent n=0 discrepancy is only the forced
zero coordinate of Mathlib completion; the right tower starts at exponent one.
The independent maintainer found an H2 ownership mismatch in the first
delivery: the reused plain data was cited through a theorem node. This repair
replaces that citation by the quotient-data and tower definition nodes. The
proof dependency is imported privately and all statement imports are public.


## New nodes

`def-sfb-adic-short-complex-quotient-tower` records existing definitions
`AdicCohomology.shortComplexTower` and `AdicCohomology.tower` in
`Sheaf.Algebra.Homology.AdicShortComplexCohomologyML`, with existing:true and
no new Lean file. The former is the actual termwise quotient diagram at
exponent n+1, with the canonical quotient transitions; the latter is its
composition with the homology functor. Both are constructions for arbitrary
modules over a commutative ring, without the finiteness and Noetherian
hypotheses needed by the theorem in the same module. The node cites
`def-sf-adic-module-quotient-data` for the underlying quotient functors,
projections and transitions. Its source is Tag 0EGU's actual quotient
complexes and quotient-cohomology system before assertion (2).

Searches repeated for this ownership record: LeanSearch for the inverse
system of termwise ideal-power quotients and its cohomology tower gave eight
hits (group cohomology, ring quotient transitions and general inverse systems),
with no exact construction; Loogle `"ShortComplex", "quotient"` gave zero;
Mathlib grep `shortComplexTower|AdicCohomology.tower` gave zero. Project rg
located exactly these definitions in AdicShortComplexCohomologyML. DAG rg
found them recorded only under two theorem nodes, with no definition owner;
the existing quotient-data definition node stops before the tower definitions.
Blueprint search `adic short complex` gave zero matches. Thus this record
adds missing DAG ownership of existing data and does not duplicate a Lean
notion or another definition node. The raw result descriptions are in its
mathlib_searches. The new node records blueprint.from.node as null, matching the actual
created.item-chain resolver. Its place retains the inherited source location
and its via retains the complete chain through the dispatched item.

## Repair of returned delivery caf70077b99e

H2 repaired in full: removed the theorem node
`lem-sfb-adic-short-complex-cohomology-ml` from stmt_deps; cited existing
`def-sf-adic-module-quotient-data`; added and cited the existing:true ownership
node `def-sfb-adic-short-complex-quotient-tower`; updated lean.note to name the
two definition owners and explain that no theorem conclusion is needed.
The Lean file and verbatim signature are unchanged from the reviewed delivery.
Compared the retained sandbox node against current main: before this repair,
only lean and stmt_deps differed, as expected for the returned delivery; the
current item still has the original two mathematical statement dependencies.
Delivery wrapper rebasing supplies the current main baseline without direct
Git operations in the read-only shared clone.

Reread the new node against both existing declaration bodies: n maps to
S.map (quotient I (n+1)), transitions use S.mapNatTrans (transition I ...),
and tower is shortComplexTower I S followed by homologyFunctor. Its sole
statement dependency is the quotient-data definition, with no theorem
statement dependency and no new theorem. The original theorem's hypotheses,
canonical component characterization and naturality clauses are unchanged;
the maintainer's independent return explicitly accepted their mathematics.


## Repair of returned delivery c8d7952c08d5

Repaired the blueprint metadata mismatch reported by review_split.py. Set
`def-sfb-adic-short-complex-quotient-tower.blueprint.from.node` to JSON null,
which is exactly `blueprint_refs.py ancestor
lem-sfb-finite-short-complex-adic-cohomology-limit` (None). I previously copied
the item's recorded from.node instead of following the resolver output;
that was the metadata error in the returned delivery.

Read blueprint_refs.py's chain and ancestor_for_item, review_split.py's
comparison, and stage2_delivery.py's new-node check. Traced created.item from
the dispatched item through all eighteen existing nodes. The last node,
lem-sfb-admissible-direct-image, has created.item equal to the module name
Sheaf.SixFunctors.CtfStabilityDirectImages, which has no DAG node. Thus the
nearest ancestor is null even though the inherited source place names the
blueprint direct-images proof. The full existing via chain is already the
computed created.item chain, so it is retained, as is the informative place.
The original item's blueprint metadata is outside the repair and is unchanged.

Compared the retained sandbox with current main and the returned metadata:
current main has the original item with lean=null, while the retained delivery
contains the same accepted Lean statement and definition ownership repair.
This repair changes the new node's ancestor field and this report; it does
not change Lean, the theorem signature, the ownership declarations, or the
previously repaired statement dependencies. The prescribed delivery wrapper
rebases these files on current main. Rechecked the new node against the
resolver contract after editing: from.node=null and via starts with the item
and follows its complete existing created.item chain. This addresses the only
point in the second return.
