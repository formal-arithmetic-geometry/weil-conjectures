## Worker report

The module `lean/Sheaf/RingTheory/FlatLocalCompletionIso.lean` states
`RingHom.flat_local_completion_iso` with proof `sorry`. No definitions or new
nodes were needed; only the item's `lean` field changes.

Hypothesis and clause correspondence:
- The rings A and B are arbitrary `Type u` and `Type v` with `CommRing`.
- Noetherianity is `[IsNoetherianRing A] [IsNoetherianRing B]`.
- Locality of the rings is `[IsLocalRing A] [IsLocalRing B]`.
- The map is `(φ : A →+* B)`; flatness is `(hflat : φ.Flat)` and locality is
  `(hlocal : IsLocalHom φ)`.
- The equality m_A B = m_B is `hmax`, using `Ideal.map φ`.
- The induced residue-field isomorphism is `hres`: a ring equivalence of the
  two maximal-ideal quotients, whose value on every quotient class is the
  quotient class of `φ a`. Quotient surjectivity makes this exactly the induced
  map's being an isomorphism, with no choice of an unrelated identification.
- A-hat and B-hat are `AdicCompletion (IsLocalRing.maximalIdeal A) A` and its
  B counterpart. Their canonical maps are the Mathlib `algebraMap`s.
- The canonical coordinate formula for φ-hat is the first conjunct: for every
  n, x, and representative a of `evalₐ m_A n x`, its image evaluates to the
  class of `φ a` modulo m_B^n. Every coordinate has a representative, so this
  determines the map uniquely. Stating existence together with this formula
  avoids introducing a second definition of an induced map.
- The isomorphism conclusion is `Function.Bijective φhat` for this ring map.
- The required equation φ-hat composed with iota_A = iota_B composed with φ is
  the final equality of composed ring homomorphisms.

Dependency declarations used and read:
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the abbreviation
  for a ring being Noetherian as its own module, equivalently every ideal FG.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, defined using φ.toAlgebra
  and `Module.Flat A B`; this renders def-weil-pbc-flat-ring-map.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, compatible
  families of module quotient classes. For the ring module these are A/m^n.
  `Mathlib.RingTheory.AdicCompletion.Algebra` supplies the ring structure,
  canonical algebra map, and `AdicCompletion.evalₐ` into A/m^n.
These are the declarations recorded on the three statement dependencies;
Algebra imports Basic, and RingHom.Flat imports the Noetherian definitions.

Edge cases: separate arbitrary universes are explicit, with no automatic
implicit binders. Fields (m = 0) and n = 0 are included; at n = 0 both quotient
coordinates are zero and the coordinate condition is automatic. Local rings
in Mathlib are nontrivial, matching the usual maximal-ideal convention in the
source; the zero ring is therefore excluded by the local-ring hypothesis,
not by an extra assumption. No domain, positive dimension, or completeness
hypothesis is added. The source was read at
https://stacks.math.columbia.edu/tag/0AGX because the local literature TeX is
absent on this machine; its statement agrees with the node. No statement
fault or correction was found.

Searches actually run:
- `msearch.py leansearch`, query `flat local ring homomorphism same residue
  fields isomorphism completions`: UNAVAILABLE, internal server error; no
  verdict is inferred from this unavailable search.
- `msearch.py leanfinder`, query `flat local map of noetherian local rings same
  residue field and maximal ideal induces isomorphism on adic completions`:
  eight hits including AdicCompletion.flat_of_isNoetherian, ofAlgEquiv,
  Module.FaithfullyFlat.of_flat_of_isLocalHom and RingHom.Flat.localRingHom;
  none states the item. ofAlgEquiv requires an already complete ring and is
  not the map between completions of two different rings.
- `msearch.py loogle`, query `AdicCompletion, RingHom.Flat, IsLocalHom`: 0 hits.
- `msearch.py grep`, query `completion.*[Ii]so|def.*map|flat.*local`, directory
  RingTheory/AdicCompletion: 13 hits, chiefly linear-map functoriality and
  tensor-product comparisons; no match for the item.
- `rg` on Mathlib AdicCompletion for maps and equivalences found liftRingHom,
  evalₐ and generic linear functoriality; full relevant APIs were read.
- `rg` on `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, pattern
  `completion.*[Ii]so|flat.*local.*completion|lem-weil-pbc-flat-local-completion-iso`:
  no hits. The source-node id and the proposed name also have no hit in
  dag/lean_names_upstream.json.
- `rg` on repository lean/Sheaf for AdicCompletion and completion isomorphisms
  found CompletionFiniteQuotient, CompletionRegularLocal and other related
  statements, but none states this node or defines a cross-ring map.

Validation: server single-file compilation succeeded with no errors or
warnings. The module includes the node's seven-step natural-language proof,
with the dependencies for each step. The second reader will write the second
reading and deliver; this worker performs only the no-push dry run.

## Second reading by M1

I reread the node statement against More on Algebra, Lemma Tag 0AGX and the Lean declaration in `lean/Sheaf/RingTheory/FlatLocalCompletionIso.lean`.

- Objects: the Lean binders `{A : Type u} {B : Type v}` with `[CommRing A] [CommRing B]` are the two commutative rings; `[IsNoetherianRing A] [IsNoetherianRing B]` and `[IsLocalRing A] [IsLocalRing B]` render Noetherian local hypotheses. `φ : A →+* B` is the ring map, `hflat : φ.Flat` its flatness, and `hlocal : IsLocalHom φ` its localness. `hmax : Ideal.map φ (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B` renders `m_A B = m_B`. `hres` supplies a ring equivalence between the two quotient residue rings and requires it to carry every class of `a` to the class of `φ a`, exactly the induced residue-field isomorphism.
- Completions are `AdicCompletion (IsLocalRing.maximalIdeal A) A` and the corresponding B object. The existential `φhat` is a ring map between them. Its first conjunct gives the node's coordinate formula for every `n`, `x`, and representative `a`; this includes `n = 0` and determines the induced map on compatible families. The second conjunct is `Function.Bijective φhat`, exactly the isomorphism conclusion. The final conjunct is the required compatibility equation, with the canonical maps rendered by `algebraMap` and composition by `.comp`.
- Quantifier order and conjunction structure match the node. No extra finiteness, domain, characteristic, completeness, or universe restriction was introduced. The separate universes `u` and `v` preserve all cases covered by the node.

Edge cases checked: `n = 0` makes both quotient coordinates trivial and the formula remains well typed; zero ideals/fields are permitted by the ideal and quotient expressions; local-ring instances enforce the standard nontrivial local-ring convention, with no additional zero-ring exclusion; arbitrary index-free completions and both ring universes remain covered.

Searches were reviewed from the worker report and repeated by reading Mathlib's `RingTheory/AdicCompletion` APIs and searching the source/project for completion isomorphisms. The LeanSearch service was unavailable in the recorded run; LeanFinder/Loogle and grep found only fixed-ring completion maps and no statement of this cross-ring result. No existing declaration matches the node.

No mismatch was found. The module and node statement required no repair; only the node's `lean` record was added for delivery. The declaration contains the required source and `(blueprint: lem-weil-pbc-flat-local-completion-iso)` docstrings and has only the permitted theorem `sorry`.

## Reviewer fix (R-flc1041)

Two hypotheses were re-spelled to the forms of the landed siblings, with the same meaning:
- `hres` is now `Function.Bijective (Ideal.quotientMap (IsLocalRing.maximalIdeal B) φ (IsLocalRing.maximalIdeal_comap φ).ge)`: the induced map A/m_A → B/m_B is bijective, as in H1 b706dfe85 (lem-weil-pbc-flat-iso-mod-ideal-powers), whose lemma the proof applies. The delivered `∃ e : … ≃+* …, ∀ a, e (mk a) = mk (φ a)` is equivalent (quotient surjectivity) but is not the shared form.
- `hlocal : IsLocalHom φ` is now the instance binder `[IsLocalHom φ]`, as in G1 346b0c248 (lem-weil-pbc-finite-after-completion), which the proof applies; it also supplies the containment for `Ideal.quotientMap`.
Everything else (Noetherian local rings, `φ.Flat`, `hmax`, the existential φhat with the componentwise formula as in G1, `Function.Bijective φhat`, φhat ∘ ι_A = ι_B ∘ φ) is unchanged; the fixed file compiles clean.
