## Worker report

The module `Sheaf.RingTheory.NormalOfFlatNormalFibers` states
`RingHom.normal_of_flat_normal_fibers`, with its sole proof `sorry`.
The node agrees with Stacks Project, Algebra, Lemma 10.163.8, Tag 0C22:
https://stacks.math.columbia.edu/tag/0C22. The local literature checkout has no
`stacks-project/algebra.tex`, so the source statement and proof were read on that page.
No statement correction, new notion, dependency module, or disputed statement is needed.

Hypothesis and conclusion correspondence:

- Commutative rings and their homomorphism: `{R : Type u} {S : Type v}`,
  `[CommRing R] [CommRing S]`, and `(φ : R →+* S)`.
- (1) R Noetherian: `[IsNoetherianRing R]`.
- (2) S Noetherian: `[IsNoetherianRing S]`.
- (3) φ flat: `(hflat : φ.Flat)`, the recorded `RingHom.Flat`.
- (4) Every fibre is normal: `hfibres` first installs precisely `φ.toAlgebra`,
  then quantifies over every `(p : Ideal R) [p.IsPrime]` and every prime ideal
  `(q : Ideal (p.Fiber S)) [q.IsPrime]`. Its conclusion is
  `IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)`.
  Mathlib's fibre is κ(p) ⊗[R] S; tensor commutativity identifies it with the
  source's S ⊗[R] κ(p), as the dependency record explicitly specifies.
- (5) R normal: `hR` quantifies over each prime p of R and says its localization
  is a domain and integrally closed.
- Conclusion S normal: the same two conditions at every prime q of S.

Dependency declarations (full signatures and docstrings read in the source checkout):

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`, from
  `Mathlib.RingTheory.Noetherian.Defs`, equivalent to every ideal finitely generated.
- `def-weil-pbc-flat-ring-map`: `RingHom.Flat`, from
  `Mathlib.RingTheory.RingHom.Flat`, defined by `Module.Flat R S` via φ.toAlgebra.
  `Module.Flat` and `Module.Flat.iff_lTensor_preserves_injective_linearMap` in
  `Mathlib.RingTheory.Flat.Basic` give the specified tensor-injectivity criterion.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` from
  `Mathlib.RingTheory.Localization.AtPrime.Basic`; `Ideal.ResidueField` from
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`; `Ideal.Fiber` from
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber` (imported).
- `def-weil-pbc-normal-ring`: its recorded inline condition, with `IsDomain`
  from `Mathlib.Algebra.Ring.Defs` and `IsIntegrallyClosed` from
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, at `Localization.AtPrime`.
  The project expressly requires this inline condition, without a named predicate.

Edge cases checked: zero rings and zero fibres have no prime ideals, so normality
is vacuous, exactly as in the source; no `Nontrivial R` or `Nontrivial S` is imposed.
Non-domain normal rings (such as products of fields) are included because only
prime localizations are required to be domains. No finite type, faithful flatness,
local-ring, characteristic, or dimension hypothesis is added. Universes u and v
are explicit and independent, and there is no quantification over test algebras
in a potentially insufficient universe. The algebra of every fibre comes from
the same φ; no unrelated algebra structure can change its meaning.

Searches made with `msearch.py J1 lem-weil-pbc-flat-normal-fibres-noetherian-normal`:

- LeanSearch: "A flat map of Noetherian rings with normal fibers and normal base
  has normal target". Service unavailable (Internal Server Error); no verdict.
- LeanFinder: "A flat map of Noetherian commutative rings with normal base and
  normal fiber rings has normal target". Eight hits, including smooth flatness,
  going-down, and Noetherian integral closures; none states normality ascent.
- Loogle: `IsIntegrallyClosed, Module.Flat`. Zero hits.
- Mathlib grep: `normal.*flat|flat.*normal|IsIntegrallyClosed` in `RingTheory/Flat`.
  Zero hits. Direct rg searches located and inspected the existing notions.
- Project source and `lean/Sheaf` rg: `normal.*flat|flat.*normal|normal.*[Ff]ibre|`
  `[Ff]ibre.*normal|lem-weil-pbc-flat-normal-fibres-noetherian-normal`. Results
  concern smooth-base-change descriptions and strongly transcendental elements,
  not this ring-theoretic theorem.
- Declaration collision and upstream-name search: `normal_of_flat|normal.*[Ff]iber|`
  `[Ff]iber.*normal|lem-weil-pbc-flat-normal-fibres-noetherian-normal` in
  `dag/lean_names_upstream.json`, `WeilConjectures`, and `lean/Sheaf`: no matching
  declaration. No existing theorem was found.

The declaration docstring carries all five proof steps: Noetherian fibres,
Serre's criterion for R and fibres, ascent of S₂, ascent of R₁, and Serre's
criterion for S. The delivery changes only the item's `lean` record.

## Second reading by J1

I independently read the repository node, its sandbox copy, all four statement
 dependency nodes, and `NormalOfFlatNormalFibers.lean`. The local Stacks checkout
is absent. I read Tag 0C22 online and downloaded the official Stacks `algebra.tex`
into this item's scratchpad. Lines 46541–46559 give exactly the node's five
hypotheses, conclusion and proof. The chapter conventions at lines 33–43 specify
commutative rings with identity and explicitly include the zero ring. The
Ascending properties section at lines 46293–46300 adds no standing assumptions.

Object, hypothesis and conclusion checklist (each verdict: exact):

1. Objects R and S are arbitrary commutative rings: `{R : Type u} {S : Type v}`
   with `[CommRing R] [CommRing S]`. The homomorphism is `(φ : R →+* S)`.
   It preserves identity as required by the source's ring convention.
2. Hypothesis (1), R Noetherian: `[IsNoetherianRing R]`.
3. Hypothesis (2), S Noetherian: `[IsNoetherianRing S]`.
4. Hypothesis (3), this homomorphism flat: `(hflat : φ.Flat)`.
5. Hypothesis (4), every prime fibre normal: `hfibres` installs
   `letI : Algebra R S := φ.toAlgebra`, then quantifies over
   `∀ (p : Ideal R) [p.IsPrime]`. The fibre is precisely `p.Fiber S`.
   Its normality is `∀ (q : Ideal (p.Fiber S)) [q.IsPrime],
   IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)`.
   Thus the second prime is a prime of the fibre, not a prime of S or R, and
   the order of quantification is the node's order.
6. Hypothesis (5), R normal: `hR` quantifies over every prime ideal p of R and
   requires `IsDomain (Localization.AtPrime p) ∧
   IsIntegrallyClosed (Localization.AtPrime p)`.
7. Conclusion, S normal: every `(q : Ideal S) [q.IsPrime]` satisfies the same
   domain-and-integral-closure conjunction for `Localization.AtPrime q`.

Dependency audit: I opened the actual declarations and docstrings in the
read-only Mathlib source, not just the recorded names. `IsNoetherianRing` in
Noetherian/Defs.lean:196 is `IsNoetherian R R`, with
`isNoetherianRing_iff_ideal_fg` spelling out exactly finite generation of all
ideals. `RingHom.Flat` in RingHom/Flat.lean:27 installs `φ.toAlgebra` and requires
`Module.Flat R S`; Flat/Basic.lean:316 gives the tensor-injectivity criterion.
`Localization.AtPrime` in Localization/AtPrime/Basic.lean:57 localizes at the
prime complement. `Ideal.ResidueField` in LocalRing/ResidueField/Ideal.lean:33
is the residue field of that localization. `Ideal.Fiber` in
LocalRing/ResidueField/Fiber.lean:66 is κ(p) tensor S over R; tensor commutativity
identifies it with the node's reversed factors, as its dependency record says.
`IsIntegrallyClosed` in IntegralClosure/IntegrallyClosed.lean:74 means integral
closure in `FractionRing`; conjoining `IsDomain` at each prime localization is
exactly the normal-ring dependency's prescribed inline formulation. None of
these dependencies needs repair or a replacement module. No new definition
nodes or dependency modules are present in this delivery.

Edge cases: zero rings and zero fibres have no prime ideals, so the corresponding
normality quantifiers are vacuous, as in Stacks. A map from the zero ring forces
its target to be zero; no nontriviality assumption is needed. Products of normal
domains are not excluded by a global domain hypothesis. Flatness is not replaced
by faithful flatness, and neither finite type nor finite presentation is assumed.
There are no restrictions on characteristic, dimension or residue fields.
Universes u and v are explicit, independently arbitrary; no test-object universe
can make a hypothesis vacuous. Empty scheme, index-set and n = 0 cases are not
additional parameters of this ring-theoretic statement.

Independent searches, using different wording from the worker:

- LeanFinder through msearch: "Integrally closed localizations ascend under a
  flat ring homomorphism whose residue field tensor products are normal".
  Eight hits concern integral closure and localization, or Zariski's Main
  Property; none states this theorem.
- Loogle through msearch: `RingHom.Flat, IsIntegrallyClosed`: zero hits.
- LeanSearch through msearch: "Serre criterion implies normality of a flat
  algebra over a normal Noetherian ring when all fibers are normal". Service
  unavailable (Internal Server Error); no mathematical verdict assigned.
- rg in Mathlib RingTheory/Flat and RingHom/Flat.lean for `integrallyclosed|normal`:
  no hits. rg in WeilConjectures, repository lean/Sheaf and
  dag/lean_names_upstream.json for normal/integrally-closed together with
  flat/fiber/fibre: unrelated deformation, fundamental-group, normalization and
  smooth-base-change passages only; no existing ascent theorem or name collision.

H5–H9 audit: the module has one named theorem with proof `sorry`, no definitions
or auxiliary proofs. Both docstrings carry the source and blueprint identifier.
The theorem docstring follows all five node proof steps: Noetherian fibres;
Serre's criterion for base and fibres; S₂ ascent; R₁ ascent; Serre's criterion
for S. Namespace, header, imports and line lengths meet the conventions.
Every variable and universe is explicitly bound. A direct comparison confirmed
that `lean.statement` is verbatim the file's signature and the node copy changes
only `lean`; there is no statement correction to audit.

Mismatches found: none. Changes: appended this independent review only; retained
the correct Lean module and node record unchanged. Remote scompile of the module
completed successfully in 1.6 seconds, exit code 0, without diagnostics.
