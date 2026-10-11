## Worker report

The module `Sheaf.RingTheory.PopescuEnlargeSolutionModulo` states
`Algebra.exists_essentiallySmooth_artinian_enlargement`, with its only proof `sorry`.
It defines no new notion. Its docstring contains all ten proof steps of the DAG node,
including the three residue-field cases and both flatness arguments.

Source checked: https://stacks.math.columbia.edu/tag/07FI, Lemma 16.11.3,
including its reference to 07FH. The local literature checkout does not contain
`smoothing.tex`; the official Stacks page supplies the statement and proof.
The node and source agree. No statement correction or disputed statement is needed.

Hypothesis-by-hypothesis correspondence (write Pbar for the displayed polynomial
localization quotient and Lbar for the displayed Lambda localization quotient):

- Field k of positive characteristic p: `(k : Type u) [Field k]`, `(p : ℕ)
  [CharP k p] (hp : 0 < p)`. Primality of p is a consequence for a field.
- Noetherian k-algebra Lambda: `(Λ : Type v) [CommRing Λ] [Algebra k Λ]
  [IsNoetherianRing Λ]`.
- Geometric regularity over k: `(hreg : IsGeometricallyRegular k Λ)`.
- Prime q and n at least one, inherited from solution-modulo:
  `(q : Ideal Λ) [q.IsPrime] (n : ℕ) (hn : 1 ≤ n)`.
- Number of variables and k-algebra map phi: `(m : ℕ)
  (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)`; m may be zero.
- p is phi inverse image of q: `q.comap φ.toRingHom`, not a separately chosen ideal.
- P is the localization at p: `Localization.AtPrime (q.comap φ.toRingHom)`.
- The induced P-to-Lambda_q map is `(ψ : Localization.AtPrime
  (q.comap φ.toRingHom) →+* Localization.AtPrime q)` with `hψ`, the equality of
  the two composites from the polynomial ring. This is the dependency's exact encoding.
- q Lambda_q = p Lambda_q: `hideal`, equality of mapped ideals along the
  localization map and its composite with phi.
- P-to-Lambda_q flat: `hflat : ψ.Flat`.
- Quotients P/p^n P and Lambda_q/q^n Lambda_q are written using `⧸` and powers of
  the mapped ideals; extension of ideals commutes with taking their powers.
  Their local Artinian properties are explicit `IsLocalRing` and `IsArtinianRing`
  binders, as in the dependency's conclusion and the node.
- D is a commutative local Artinian ring: `(D : Type w) [CommRing D]
  [IsLocalRing D] [IsArtinianRing D]`. No size restriction ties D to k or Lambda.
- First arrow Pbar-to-D: `[Algebra Pbar D]` and its `algebraMap`, with
  `[IsLocalHom (algebraMap Pbar D)]` and `hsmooth : EssentiallySmooth Pbar D`.
- Second arrow D-to-Lbar: `(g : D →+* Lbar) [IsLocalHom g]` and `hgflat : g.Flat`.
- These arrows factor the induced quotient map: `hfactor`, equality after
  precomposing with the surjective quotient map P-to-Pbar. This gives exactly
  the equality on Pbar, without introducing a second quotient map definition.
- Chosen lambda outside q: `(l : Λ) (hl : l ∉ q)`; `l` is the Lean name of lambda.
  The finite subset E of the preceding existence theorem is not part of this
  node's hypotheses: this lemma takes the already chosen factorization.

Conclusion clause-by-clause correspondence:

- Positive integer exponent: `∃ (r : ℕ), 0 < r ∧ ...`. Positive naturals encode
  exactly the positive integers in the node (r avoids conflating the exponent with q).
- New ring and first arrow: `∃ (D' : Type (max u v w)) (_ : CommRing D')
  (_ : Algebra D D')`; the first arrow is `algebraMap D D'`.
- New second arrow: `(g' : D' →+* Lbar)`.
- D' local Artinian: `IsLocalRing D' ∧ IsArtinianRing D'`.
- Both new arrows local: `IsLocalHom (algebraMap D D') ∧ IsLocalHom g'`.
- First essentially smooth, second flat: `EssentiallySmooth D D' ∧ g'.Flat`.
- Factorization of the given arrow: `g'.comp (algebraMap D D') = g`.
- Image of lambda^r in Lbar belongs to image of D': the quotient map applied to
  `(algebraMap Λ (Localization.AtPrime q)) (l ^ r)` belongs to `Set.range g'`.
  This specifies the element and the map, rather than asserting only an abstract
  containment of unrelated rings.

Dependency declarations read and used:

- `Sheaf.RingTheory.PopescuSolutionModulo`,
  `Algebra.exists_essentiallySmooth_artinian_factorization_mod_prime_pow`:
  its full signature and docstring determine the explicit setup, including the
  induced-map and factorization equations. The new module imports this module.
  A statement module does not invoke the dependency's existence proof: its
  conclusion is unpacked as this lemma's input data.
- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`: every ideal finitely generated.
- `Sheaf.RingTheory.GRing`, `Algebra.IsGeometricallyRegular`: geometric regularity
  over k (not the different `IsGRing` predicate in the same dependency record).
- `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`: flatness for each named ring map.
- `Sheaf.RingTheory.EssentiallySmooth`, `Algebra.EssentiallySmooth`: localization
  of a smooth algebra up to algebra isomorphism. All these imports are inherited
  from `PopescuSolutionModulo`; no private copies are introduced.

Edge cases checked: m = 0 is allowed by Fin 0; n = 1 is allowed, while n = 0 is
excluded as in 07FH; every prime including q = 0 is allowed. A zero Lambda has
no prime q, and zero Artinian rings cannot meet the local-map setup to the
nonzero quotient. The field characteristic condition excludes characteristic zero.
No finite-type, separability, or algebraicity assumption is imposed on the residue
field element: the docstring covers membership in the residue subfield,
transcendental elements, and inseparably algebraic elements. For a unit already in
D's image, the identity enlargement is allowed. r = 0 is excluded. The universe w
of D is independent; D' lives in the common universe max u v w, sufficient for the
polynomial localizations and finite etale extensions in the proof. No independent
smaller test universe or empty family creates a vacuous hypothesis.

Searches made before writing:

- msearch LeanFinder: `Enlarge a local Artinian essentially smooth factorization
  modulo a prime power so a positive power of a given unit is in its image`.
  Eight hits, including perfectoid untilts, smooth-locus localization, Henselian
  rings and standard-etale lifting. None states this enlargement lemma.
- msearch Loogle: `IsLocalHom, RingHom.Flat`: zero hits.
- msearch grep (Mathlib RingTheory):
  `enlarge.*solution|solution.*modulo|EssentiallySmooth`: zero hits.
- msearch LeanSearch: `local Artinian ring essentially smooth extension containing
  power of unit`: service unavailable (Internal Server Error), no verdict assigned.
  LeanFinder and source grep completed independently.
- rg in upstream WeilConjectures and project lean/Sheaf:
  `enlarge|solution.modulo|exists_essentiallySmooth|lem-weil-pbc-popescu-enlarge-solution-modulo`.
  Found the recorded solution-modulo statement and narrative uses in
  `PopescuResolveCharP`, plus unrelated enlargement statements; no existing
  declaration for this lemma.
- rg for the item id and `exists_essentiallySmooth_artinian_enlargement` in
  `dag/lean_names_upstream.json` and upstream WeilConjectures: zero hits.
- Read the recorded dependency modules and Mathlib Noetherian and flat-map
  definitions directly, including their signatures and docstrings.

Validation: `scompile.py` compiled the module in 2.4 seconds with exit code 0
and no warnings. `deliver2.py --no-push` printed OK: the module compiles and the
preflight passes except for the independent second reading, which the second
reader supplies. Nothing was pushed.

## Second reading by F1

I independently opened the item node and delivered module, all five statement
 dependency nodes, and the signatures/definitions in PopescuSolutionModulo,
GRing, EssentiallySmooth, Mathlib Noetherian.Defs, RingHom.Flat, and
Algebra.Group.Units.Hom. The local Stacks checkout is absent. I fetched official
stacks/stacks-project master smoothing.tex into the sandbox scratchpad and read
Section `section-inseparable`, `lemma-solution-modulo` (07FH), and
`lemma-enlarge-solution-modulo` (07FI), including the proofs. The section has no
additional standing hypotheses. The official tag pages corroborate this text:
https://stacks.math.columbia.edu/tag/07FI and
https://stacks.math.columbia.edu/tag/07FH.

My object/hypothesis/conclusion checklist follows. A denotes the displayed
polynomial localization quotient in the signature; B denotes the displayed
Lambda localization quotient. These are report abbreviations, not Lean notions.

1. Field k of characteristic p > 0: `(k : Type u) [Field k]`, `(p : ℕ)`
   `[CharP k p] (hp : 0 < p)`. Exact; positive field characteristic is prime
   without an additional hypothesis.
2. Noetherian geometrically regular k-algebra Lambda: `(Λ : Type v)`
   `[CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ]` and
   `(hreg : IsGeometricallyRegular k Λ)`. Exact. I read the dependency's
   `Algebra.IsGeometricallyRegular`, not its different `IsGRing` declaration:
   it tests regularity after finite purely inseparable field extension.
   Mathlib's Noetherian predicate means finite generation of every ideal.
3. Prime q and integer n at least one: `(q : Ideal Λ) [q.IsPrime]`, `(n : ℕ)`
   `(hn : 1 ≤ n)`. Exact, including the inherited conditions from 07FH.
4. Number of variables and k-algebra map: `(m : ℕ)` and
   `(φ : MvPolynomial (Fin m) k →ₐ[k] Λ)`. Exact. The prime p is the contracted
   `q.comap φ.toRingHom`; P is its `Localization.AtPrime`. These are the same
   objects as in the dependency, not another prime or presentation.
5. Induced map P → Lambda_q: the ring homomorphism binder `ψ` and equation
   `hψ` identify its composite with the polynomial localization map with φ
   followed by Lambda → Lambda_q. Exact by localization's uniqueness property;
   this does not permit an unrelated ring map.
6. q Lambda_q = p Lambda_q and flatness of P → Lambda_q: `hideal` maps the
   two ideals along their respective maps into Lambda_q; `hflat : ψ.Flat`
   uses flatness for the actual induced map. Both exact.
7. A = P/p^nP and B = Lambda_q/q^n Lambda_q: the explicit quotient types use
   the nth powers of mapped ideals. Ideal extension commutes with powers.
   Their `IsLocalRing` and `IsArtinianRing` binders render the node's local
   Artinian rings explicitly, as does the recorded dependency conclusion.
   Exact, with no added finiteness assumption on the residue fields.
8. Intermediate ring D and first arrow A → D: `(D : Type w) [CommRing D]`
   `[IsLocalRing D] [IsArtinianRing D] [Algebra A D]`, the arrow
   `algebraMap A D`, its `IsLocalHom` binder, and `hsmooth : EssentiallySmooth
   A D`. Exact: an algebra structure over a commutative ring is precisely a
   ring homomorphism. The dependency defines EssentiallySmooth using an
   algebra isomorphism to a localization of a smooth algebra, as required.
9. Second arrow D → B, local and flat: `(g : D →+* B) [IsLocalHom g]` and
   `hgflat : g.Flat`. Exact. I read IsLocalHom's unit-reflection definition;
   on local rings it is the usual maximal-ideal condition. RingHom.Flat is
   Module.Flat for the algebra structure of the named homomorphism.
10. These arrows factor the induced A → B map: `hfactor` compares their
    composites after the quotient map P → A with the quotient map to B
    composed with ψ. Exact since P → A is surjective; the equality is
    equivalent to equality of maps out of A, not an extra compatibility.
11. For every lambda outside q: `(l : Λ) (hl : l ∉ q)` before the existential
    conclusion. Exact quantifier order. E in 07FH is not an extra restriction
    here: every given factorization meets its empty-finite-set condition.
12. Positive integer exponent: `∃ (r : ℕ), 0 < r ∧ ...`. Exact; r distinguishes
    the exponent from the prime q and characteristic p.
13. New ring and arrows: `∃ (D' : Type (max u v w)) (_ : CommRing D')`
    `(_ : Algebra D D') (g' : D' →+* B), ...`. Exact. The first new arrow is
    `algebraMap D D'`; the second is the specified g', with no silently
    substituted inclusion or privately defined map.
14. Local Artinian D' and local arrows: `IsLocalRing D' ∧ IsArtinianRing D' ∧`
    `IsLocalHom (algebraMap D D') ∧ IsLocalHom g'`. Exact; D and B already
    carry their local Artinian structures in the hypotheses.
15. First new arrow essentially smooth and last flat: `EssentiallySmooth D D'`
    and `g'.Flat`. Exact, using the same dependency definitions, without
    adding a finite or etale condition to the conclusion.
16. Factorization of the fixed D → B map: `g'.comp (algebraMap D D') = g`.
    Exact; combining this with hfactor also gives the longer displayed
    factorization from A in 07FI.
17. Image of lambda^r belongs to the image of D': the final clause applies
    B's `Ideal.Quotient.mk` to `(algebraMap Λ (Localization.AtPrime q))
    (l ^ r)` and asserts membership in `Set.range g'`. Exact for the actual
    element and arrow; no abstract or weaker containment replaces it.

Edge cases: `Fin 0` allows no polynomial variables; n = 1 is included and
n = 0 excluded exactly as in 07FH. q = 0 is allowed whenever prime; a zero
Lambda has no prime q. Quotients by positive powers of localized maximal ideals
are nonzero; the local-map setup admits no accidental zero D. Characteristic
zero is excluded by the source, and every positive field characteristic is
admitted. No algebraicity or separability of lambda's residue is assumed: the
three residue-field cases are all present in the proof. The empty finite subset
from 07FH adds no hypothesis. There is no scheme or limit index parameter.
The universes u, v, w are independent; D' in their maximum accommodates
polynomial localizations and finite etale extensions in the proof, so no source
construction is excluded by the witness universe. An identity enlargement and
exponent 1 are allowed when sufficient; exponent 0 is correctly excluded.

Independent searches with other words than the worker's:

- msearch LeanFinder: `Flat local Artinian algebra enlargement with essentially
  smooth map and power in image`: eight smoothness/flatness/descent hits, none
  stating the required factorization and power-in-image conclusion.
- msearch Loogle: `IsArtinianRing, IsLocalHom`: zero hits.
- msearch LeanSearch: `Enlarge Artinian factorization to include a power of a
  residue field element`: service unavailable (Internal Server Error), recorded
  as unavailable, not a negative verdict.
- rg over Mathlib RingTheory, upstream WeilConjectures and project lean/Sheaf
  for `artinian.*enlarge|enlarge.*artinian|power.*image|solution_modulo`:
  unrelated polynomial/power-series facts and preceding factorization material;
  no declaration for this lemma. A further rg for
  `enlarg|Artinian.*factor|factor.*Artinian|residue.*power` in RingTheory found
  narrative applications in PopescuResolveCharP, not a duplicate statement.
- rg for `07FI|enlarge.solution|artinian_enlargement` in
  dag/lean_names_upstream.json, upstream WeilConjectures and project lean/Sheaf:
  only source references/narrative applications; no existing declaration to
  substitute for the delivered module.

H4/H5/H6/H8/H9: no new notions or private copies, no new nodes or dependency
modules, and no hollow data. The single named theorem has proof `sorry`.
The imported module supplies the recorded statement dependency and definitions.
The module and theorem docstrings identify 07FI and the blueprint item; the
proof docstring carries all ten node steps, including the two flatness
arguments and all residue-field cases. The p-power wording in step 2 correctly
repairs the source proof's imprecise exponent wording without changing the
statement. All variables/universes are bound with autoImplicit disabled;
line lengths and namespace conventions comply. No statement_change is present
or needed. I found no mismatch and left the correct Lean and node unchanged.
The second reading changes only this report and the independent search record.

Validation: the independent scompile.py run compiled the delivered module in
2.5 seconds with exit code 0 and no warnings.
The recorded lean.statement matches the file signature (including its multiline
formatting; whitespace normalization agrees with the project's signature reader).
The second-reader deliver2.py --no-push run printed OK: preflight and server
compilation passed, with no second-reading exception.
