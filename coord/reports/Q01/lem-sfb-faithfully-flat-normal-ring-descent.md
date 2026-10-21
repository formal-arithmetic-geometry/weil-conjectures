## Worker report

The module `Sheaf.RingTheory.FaithfullyFlatNormalRingDescent` states
`Algebra.normal_ring_of_faithfullyFlat`, with `sorry` as its only proof.
It is the unrestricted Stacks Project Tag 033G, read in
`literature/stacks-project/algebra.tex`, lemma-descent-normal.
No new definitions, new nodes, dependency repairs or statement corrections are needed.
The Q07 merge recorded in the ledger was a stage-1 split; the current node has
no `lean` record. This delivery adds only that record and its Lean module.

Clause-by-clause correspondence:

- The commutative rings R and S are `(R : Type u) (S : Type v)` with
  `[CommRing R] [CommRing S]`. The universes are declared explicitly and independently.
- The ring map R -> S is represented by `[Algebra R S]`, with its canonical
  `algebraMap R S`. Every unital commutative ring map supplies this algebra structure;
  this is the faithfully-flat-ring-map convention in `coord/STATE.md`.
- Faithful flatness is `[Module.FaithfullyFlat R S]`, the recorded definition of
  `def-weil-pbc-faithfully-flat-ring-map`, not a stronger property of the map.
- Normality of S is precisely `hS : ∀ (q : Ideal S) [q.IsPrime],
  IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)`.
  The first conjunct makes each localization a domain; the second says all elements
  integral over it in its fraction ring belong to it.
- Normality of R is exactly the same quantified conjunction for each prime ideal p
  of R in the conclusion. This is the inline form explicitly recorded in
  `def-weil-pbc-normal-ring` and required by the NORMAL RING convention.
- No Noetherian, domain, finite-type, locality or nontriviality assumption occurs.
  The comments about zero rings in the node are edge-case explanations, not additional
  conclusions or assumptions; the unrestricted quantified formula includes them.

Dependency declarations read and used:

- `def-weil-pbc-faithfully-flat-ring-map`: `Module.FaithfullyFlat` from
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`; its class extends flatness and requires
  proper maximal-ideal scalar extension. The node records its equivalence with exactness
  detection. `RingHom.FaithfullyFlat` and `faithfullyFlat_algebraMap_iff` were also read
  in `Mathlib.RingTheory.RingHom.FaithfullyFlat` to check the algebra-map formulation.
- `def-weil-pbc-normal-ring`: the recorded inline conjunction of `IsDomain`,
  `IsIntegrallyClosed` from `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, and
  `Localization.AtPrime` from `Mathlib.RingTheory.Localization.AtPrime.Basic`.
  `IsIntegrallyClosed` is the actual abbreviation for integral closure in `FractionRing`;
  `Localization.AtPrime` is the localization at the complement of a prime ideal.
- Proof leaves: `Ideal.exists_isPrime_liesOver_of_faithfullyFlat`,
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`, and
  `Ideal.comap_map_eq_self_of_faithfullyFlat` from
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`, together with
  `RingHom.Flat.localRingHom` from `Mathlib.RingTheory.RingHom.Flat`.
  Both modules are plain proof imports. The complete six-step node proof is in the
  theorem docstring, with the exact dependency ids and principal-ideal descent argument.

Edge cases checked before writing:

- R = S = 0: no prime ideals, so both normality predicates are vacuous; the self-map
  is faithfully flat. No `Nontrivial` binder excludes it.
- S = 0 over nonzero R: faithful flatness is impossible by injectivity of the algebra
  map. Thus the empty spectrum of S does not give a spurious counterexample.
- R = k × k and S = R under the identity: both prime localizations are fields;
  the statement does not incorrectly require R or S themselves to be domains.
- Identity maps, field extensions, and faithfully flat maps such as Z -> Z[i] fit
  without finiteness, locality, characteristic or universe restrictions.
- Prime localization over non-Noetherian rings remains the same quantified formula;
  no optional Noetherian hypothesis from the flat localization lemma is imported
  into the theorem signature.

Searches made (2026-10-22, via the prescribed `msearch.py` wrapper):

- LeanFinder: “Normality of a commutative ring descends along a faithfully flat ring
  homomorphism” returned eight hits: going down, faithful-flat base-change stability,
  prime lifting, descent of injectivity/surjectivity/bijectivity, flatness and composition.
  None concludes normality of R from normality of S.
- Loogle: `"IsIntegrallyClosed", "FaithfullyFlat"` returned zero hits.
- Mathlib grep: `IsNormalRing|NormalRing|normal.*descent|descent.*normal` returned zero hits.
- LeanSearch: “Normality descends along faithfully flat ring maps, normal means every
  prime localization is an integrally closed domain” returned faithful flatness, its
  injectivity/flatness/spectrum criteria, and going down. None is the desired theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for normality and faithful-flatness,
  descent and `NormalRing` found etale/smooth ascent, filtered-colimit results and
  `Algebra.normal_ring_of_normal_tensor_field` in
  `Sheaf.RingTheory.NormalRingFieldExtensionDescent`. I read that declaration: it only
  concerns B -> B tensor_F E for a field extension F -> E, so it is not the arbitrary
  faithfully flat ring-map theorem. Its domain-level helper is private and assumes
  both rings are domains; it also does not state this node.
- Exact searches for `normal_ring_of_faithfully`, `normal_of_faithfully`, and
  `descent_normal` found no declaration; the chosen public name has no clash.
- `grep -rn` for the item id in `lean/WeilConjectures` returned no hits.
- The existing DAG node `lem-per-faithfully-flat-normal-ring-descent` has the same
  mathematical statement but no usable recorded Lean declaration. It is not duplicated
  by a new node in this delivery; existing node consolidation remains maintainer work.

No STATEMENT-DISPUTED issue or mathematical node fault was found. The previous worker's
stage-1-already-merged rejection does not establish a stage-2 statement exists; the dry run
will check the actual stage-2 packet with its newly added `lean` record.

Validation: the delivered file is compiled through `scompile.py`; the dry run and final
push use `deliver2.py`, both with this item and group Q01. Only the sandbox is edited.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
