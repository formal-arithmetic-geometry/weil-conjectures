## Worker report

The node is already stated exactly by
`Algebra.WeaklyEtale.bijective_localRingHom_of_isMaximal_of_isStrictlyHenselianLocalRing`
in `Sheaf.RingTheory.StrictHenselianMaximalLocalRingIso`. Its source is
`lean/Sheaf/RingTheory/StrictHenselianMaximalLocalRingIso.lean`, originally written by Q32.
I opened the complete module and independently confirmed the identical current published
source using `scompile.py --source Sheaf.RingTheory.StrictHenselianMaximalLocalRingIso`.
This delivery records it with `existing: true`, branch `newtargets-dag`, and supplies no
new module or duplicate declaration. Only the item's `lean` field changes.

The source statement was checked against
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-pe-wc-rings/det-pe-wc-rings-local-iso.md`.
There are no statement dependencies (`stmt_deps: []`). No definition, hypothesis,
conclusion, proof dependency, or natural-language statement is changed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative rings and the specified ring map `R → B` are
  `{R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]`;
  the map is `algebraMap R B`. An arbitrary commutative ring homomorphism gives this
  algebra structure via `RingHom.toAlgebra`; no injectivity or finiteness is assumed.
- Weak etaleness is `[Algebra.WeaklyEtale R B]`, the Mathlib notion of flatness of
  the algebra and its multiplication map. The parenthetical ind-etale example is
  an example, not an additional hypothesis or a second conclusion.
- The specified maximal ideal is `(m : Ideal R) [m.IsMaximal]`.
  Its prime instance is inferred from maximality; it is not a new assumption.
- Strict henselianity of exactly `R_m` is
  `[IsStrictlyHenselianLocalRing (Localization.AtPrime m)]`.
  This does not require the original ring `R` to be local or strictly henselian.
- The prime of the target is `(n : Ideal B) [n.IsPrime]`.
- Contraction to the specified maximal ideal is
  `(hmn : m = n.comap (algebraMap R B))`, the symmetry of `n ∩ R = m`.
- The conclusion is
  `Function.Bijective (Localization.localRingHom m n (algebraMap R B) hmn)`.
  `Localization.localRingHom` is the canonical homomorphism between the two
  localizations, induced by the given algebra map, rather than an arbitrary map.
  Bijectivity of that ring homomorphism is exactly its being a ring isomorphism;
  `RingEquiv.ofBijective` provides the corresponding equivalence with that same map.

The signature recorded in `lean.statement` is copied verbatim from the theorem keyword
up to, but not including, `:=`. The module explicitly declares `universe u v` and
binds every variable; the rings may have independent universes.

Definitions and proof interfaces inspected:

- `Mathlib.RingTheory.Etale.Weakly`: `Algebra.WeaklyEtale`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  `Localization.localRingHom`, and its normalization `localRingHom_to_map`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`.
- The existing module imports the node's stated proof dependencies privately:
  `Sheaf.RingTheory.IndEtaleStability`, declaration
  `RingHom.indEtale_principalZariski_stability`, and
  `WeilConjectures.RingTheory.ProEtale.HenselianLocalRing`, declaration
  `Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing`.
  Its docstring gives the complete four-step localization/Olivier proof plan and
  names both DAG proof dependencies. Its existing theorem proof is `sorry`, as
  appropriate for stage 2; this report makes no claim that this theorem is proved.

Edge cases checked: neither ring is assumed Noetherian, finite dimensional, a field,
or reduced; there is no restriction on characteristic. The zero source ring has no
maximal ideal and the zero target ring has no prime ideal, so those impossible
hypothesis combinations are correctly excluded by the ideals, rather than by an
extra `Nontrivial` assumption. The identity map and the strictly henselian field case
are included. The prime `n` need not be maximal, as in the node. Both universes are
arbitrary and independent. No index set or degree occurs in this statement.

Searches (all through the prescribed tooling, or read-only source searches):

- `msearch.py ... leansearch "The local rings of a weakly etale algebra over a strictly
  henselian maximal ideal are isomorphic"`: eight hits on etale locality,
  localization, and henselian locality; no matching Mathlib theorem.
- `msearch.py ... leanfinder "A weakly etale algebra induces an isomorphism of
  localizations at a prime over a strictly henselian maximal ideal"`: eight hits on
  etale loci/localizations and formal etaleness; no exact Mathlib theorem.
- `msearch.py ... loogle "Localization.localRingHom, Function.Bijective"`: three
  hits, concerning saturated subalgebras, finite unramified algebras, and conductors;
  none has this node's hypotheses.
- `msearch.py ... grep
  "bijective.*localRingHom|WeaklyEtale.*StrictlyHenselian|StrictlyHenselian" RingTheory`:
  six hits on canonical local-ring maps, none with the strict henselian hypothesis.
- `rg` in `WeilConjectures/` for `bijective_localRingHom|strictly henselian.*weakly|stalkwise
  version` found
  `Algebra.WeaklyEtale.bijective_localRingHom_of_isStrictlyHenselianLocalRing`
  in `WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale`, line 245. I read its full
  signature, docstring, ambient binders, and proof. It is the more general
  prime-contraction version and was the previous worker's attachment candidate;
  it shares one ring universe and omits an explicitly named maximal ideal.
- `grep -rn "det-pe-wc-rings-local-iso" WeilConjectures/` found no literal node-id
  occurrence. Searching `dag/lean_names_upstream.json` for the upstream theorem
  name found no entry; the actual source and node audit nevertheless record it.
- `rg` in `lean/Sheaf/` for `bijective_localRingHom|det-pe-wc-rings-local-iso` found
  the already published Q32 module above. Its theorem matches every explicit
  hypothesis and the canonical-map conclusion without replacing the statement
  by the more general upstream formulation. Reusing this existing declaration
  avoids defining or stating the same notion a second time.

No new nodes, dependency modules, statement correction, or statement dispute.
The required dry run compiles a real `#check @` probe for the existing declaration
through `scompile.py`, then runs the server preflight. The independent second
reader supplies the second-reading section and performs delivery.

## Second reading by Q35

I independently opened the node copy, the blueprint source, and the published
declaration `Algebra.WeaklyEtale.bijective_localRingHom_of_isMaximal_of_isStrictlyHenselianLocalRing`
in `Sheaf.RingTheory.StrictHenselianMaximalLocalRingIso`. The source place is Stacks
More on Algebra, Theorem Olivier, Tag 092Z. The node has no `stmt_deps`; its two proof
dependencies are used only in the postponed proof.

Checklist against the node, in order:

- The rings `R` and `B` are rendered by independent universes and
  `[CommRing R] [CommRing B]`; `[Algebra R B]` supplies the specified map
  `algebraMap R B`. This is exact, with no finiteness or injectivity assumption.
- Weak étaleness is exactly `[Algebra.WeaklyEtale R B]`. The node's ind-étale phrase is
  an example and introduces no extra hypothesis.
- The chosen maximal ideal is `(m : Ideal R) [m.IsMaximal]`; strict henselianity is
  `[IsStrictlyHenselianLocalRing (Localization.AtPrime m)]`. Thus the maximality and
  the localization named by the node are both retained.
- The chosen target prime is `(n : Ideal B) [n.IsPrime]`, with the contraction equation
  `(hmn : m = n.comap (algebraMap R B))`. The equality is oriented for the canonical
  localization API and is equivalent to `n ∩ R = m`.
- The conclusion is exactly `Function.Bijective` for
  `Localization.localRingHom m n (algebraMap R B) hmn`, the canonical induced map
  `R_m → B_n`; no arbitrary map or chosen inverse is introduced. Bijectivity is the
  Lean expression of the stated ring isomorphism.

No mismatch was found, so no file or node statement was changed. In particular, the
nearby upstream theorem with one ring universe and an implicit contraction is more
general, but it is not the declaration bound here; the published declaration preserves
the node's explicit `m`, maximality, contraction equality, and independent universes.
The declaration's docstring gives the node's four proof steps (weak étale stability,
base change and localization, composition/locality, then Olivier), and its proof is
`sorry` as required for a stage-2 statement. All variables and universes are bound.

Edge cases checked: zero rings cannot provide the required maximal/prime ideals, so no
extra `Nontrivial` assumption is present; the identity map and strictly henselian field
case are included; `n` need not be maximal; every characteristic is allowed; and the
two ring universes are independent. There is no index or degree parameter, so empty
index and `n = 0` cases do not arise.

Independent searches were run with `msearch.py`: LeanSearch for the full local-ring
claim (eight ordinary étale/henselian hits, no exact theorem), LeanFinder for the
weakly-étale localization claim (eight hits, no exact theorem), Loogle for
`Localization.localRingHom, Function.Bijective` (three unrelated localization results),
and grep over Mathlib, `WeilConjectures/`, and `lean/Sheaf/`. The grep search found the
published declaration used here and the distinct, more general upstream contraction
theorem; no duplicate exact declaration exists. The existing declaration was also
checked with `scompile.py --source Sheaf.RingTheory.StrictHenselianMaximalLocalRingIso`.
