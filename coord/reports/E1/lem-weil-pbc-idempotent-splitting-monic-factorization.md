## Worker report

The module `Sheaf.RingTheory.MonicFactorizationOfIdempotent` states
`Polynomial.exists_monic_factorization_of_idempotent`, with proof `sorry`.
No definition, additional theorem, new node, dependency module, or statement correction
is needed. There are no `stmt_deps` in the assigned node.

Source checked: Stacks Project Tag 09XI, proof of (3) implies (1), specifically the
paragraph beginning with the monic polynomial and ending with its lifted monic
factorization. The local `literature/stacks-project/more-algebra.tex` is absent on this
machine, so I read https://stacks.math.columbia.edu/tag/09XI directly. This source agrees
with the node. Its characteristic-polynomial construction is the proof route, not an
additional requirement on the existential witnesses. All five node proof steps,
including their supporting node names and the zero-ring case, are in the docstring.

Hypothesis and conclusion correspondence:

- A commutative ring: `{A : Type u} [CommRing A]`, with explicitly bound universe `u`.
- An ideal contained in the Jacobson radical: `(I : Ideal A)` and
  `hI : I ≤ Ideal.jacobson (⊥ : Ideal A)`.
- A monic polynomial f: `(f : A[X]) (hf : f.Monic)`.
- Its coefficient reduction: `f.map (Ideal.Quotient.mk I)`, with coefficients in `A ⧸ I`.
- The specified factors: `(g₀ h₀ : (A ⧸ I)[X])`, `hg₀ : g₀.Monic`, `hh₀ : h₀.Monic`.
- They generate the unit ideal: `hcoprime : IsCoprime g₀ h₀`. Mathlib defines this as
  existence of coefficients a,b with `a * g₀ + b * h₀ = 1`, exactly the unit-ideal condition.
- The factorization of the reduction: `hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀`.
- B = A[T]/(f): `AdjoinRoot f`, Mathlib's actual quotient by the principal ideal `(f)`.
- The specified reduced idempotent and lifting condition: the node introduces the
  uniquely characterized Chinese remainder element with residues 1 modulo g₀ and 0
  modulo h₀. `he₁` and `he₀` require precisely these two residues for e. The canonical
  maps are `AdjoinRoot.map (Ideal.Quotient.mk I) f g₀ ...` and the analogous map to h₀.
  These send coefficients to their reductions and the class of T to the class of T,
  and factor through B/IB. Under the canonical identification with the reduced
  polynomial quotient, the two residues jointly specify exactly the element (1,0).
  Thus no arbitrary CRT isomorphism or stronger lifting hypothesis is introduced;
  the redundant name for that uniquely specified element is eliminated.
  The map divisibility certificates are obtained by equality transport from
  `dvd_mul_right g₀ h₀` and `dvd_mul_left h₀ g₀` using `hfactor`.
- The lifted element is idempotent: `(e : AdjoinRoot f) (he : IsIdempotentElem e)`;
  Mathlib defines this as `e * e = e`.
- There are monic g,h over A: `∃ g h : A[X], g.Monic ∧ h.Monic ∧ ...`.
- Their product is f: `f = g * h`.
- Their images are respectively g₀ and h₀: the two final conjuncts are
  `g.map (Ideal.Quotient.mk I) = g₀` and `h.map (Ideal.Quotient.mk I) = h₀`.
- The parenthetical explanation about constant ranks and characteristic polynomials
  is rendered in the proof docstring, in steps 2–5, as in the node's own proof.

Mathlib declarations read and used (no project dependency declarations):
`Mathlib.RingTheory.AdjoinRoot`: `AdjoinRoot`, `AdjoinRoot.map`;
`Mathlib.RingTheory.Jacobson.Ideal`: `Ideal.jacobson`;
`Mathlib.RingTheory.Coprime.Basic`: `IsCoprime`;
`Mathlib.Algebra.Group.Idempotent`: `IsIdempotentElem`.
Also the standard `Polynomial.Monic`, `Polynomial.map`, `Ideal.Quotient.mk`,
`dvd_mul_right`, and `dvd_mul_left` are used. The four imports provide the actual
notions in the signature and no private version is defined.

Edge cases checked before writing: no `Nontrivial A`, local-ring, domain, Henselian,
positive-degree, or nonzero-factor hypothesis is imposed. When A is the zero ring,
all polynomial equalities hold and monicity means leading coefficient equals 1=0,
so the claim remains valid. Degree-zero monic factors are allowed; their quotient
is the zero ring, and the relevant residue condition correctly reduces to its
unique equality. In particular f=1 and g₀=h₀=1 are allowed. I=0 is allowed and
recovers an ordinary CRT splitting over A. If I is top, the Jacobson hypothesis
forces the zero-ring case; it is not excluded. Arbitrary commutative rings,
characteristics, and object universes are covered.

Searches for an existing statement:

- `msearch.py ... leanfinder` with query "An idempotent in A[X]/(f) lifting the
  Chinese remainder idempotent modulo an ideal in the Jacobson radical yields a
  monic factorization lifting relatively prime factors": eight hits, chiefly
  `Polynomial.UniversalCoprimeFactorizationRing` constructors and their universal
  properties. None assert factorization from a lifted idempotent.
- `msearch.py ... loogle` with `AdjoinRoot.map, IsIdempotentElem, Polynomial.Monic`:
  zero hits.
- `msearch.py ... leansearch` with "idempotent splitting monic polynomial quotient
  lifting factorization Jacobson radical": service unavailable, Internal Server
  Error. This is recorded as unavailable, without a mathematical verdict.
- `msearch.py ... grep` with
  `idempotent.*factor|factor.*idempotent|charpoly.*idempotent|IsIdempotentElem.*charpoly`
  in `RingTheory`: zero hits.
- `rg` with idempotent/factor patterns in `WeilConjectures` and `lean/Sheaf`:
  unrelated product decompositions and pro-etale topology, no matching theorem.
- `rg` for the exact node id in `WeilConjectures` and `dag/lean_names_upstream.json`:
  no hits. `rg` for monic/factor combinations in `lean/Sheaf/RingTheory` finds
  `FilteredColimitHenselianPair`, which states a different result about colimits.
- Direct reads of Mathlib's AdjoinRoot, coprimeness, Jacobson radical, and idempotent
  definitions establish that all notions used already exist. The declaration name
  is new and the preflight checks name collisions.

Validation: `scompile.py E1 lem-weil-pbc-idempotent-splitting-monic-factorization`
compiled the module on the server in 1.4 seconds, exit code 0, no warnings or errors.
No statement dispute or node fault was found. Delivery remains for the second reader.

## Second reading by E1

Read the sandbox node, its complete five-step proof, the Lean module, and the
Mathlib definitions independently. The node has no statement dependencies, no
statement_change, and this delivery has no new nodes or dependency modules.
The node and Lean statement are correct; no mathematical or convention mismatch
was found. Only this second-reading report and independent search records were added.

Source: the local Stacks .tex is absent. Read the actual upstream
[more-algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex),
section-henselian-pairs (lines 2194–2204), lemma-characterize-henselian-pair
(lines 2353–2429), and [Tag 09XI](https://stacks.math.columbia.edu/tag/09XI).
The section introduces arbitrary pairs (ring, ideal); it adds no Noetherian,
local, domain, characteristic, or positive-degree condition. The relevant proof
first obtains containment in the Jacobson radical and then uses a single lifted
idempotent. The node correctly extracts that argument: universal lifting of
idempotents, or a Henselian-pair assumption, is unnecessary once this lift is given.
The source's characteristic-polynomial witnesses explain the proof construction;
the parenthetical in the node is explanatory, not a further existential conclusion.

Object, hypothesis, and conclusion list, matched item by item:

1. A commutative ring A: `{A : Type u} [CommRing A]`. Verdict: exact;
   `universe u` is explicitly declared and unrestricted.
2. An ideal I contained in the Jacobson radical of A: `(I : Ideal A)` and
   `(hI : I ≤ Ideal.jacobson (⊥ : Ideal A))`. Verdict: exact. Read
   Jacobson/Ideal.lean:65: this is the infimum of all maximal ideals containing
   the zero ideal, hence the ring's Jacobson radical.
3. A monic f in A[T]: `(f : A[X]) (hf : f.Monic)`. Verdict: exact, with only
   the indeterminate's name changed; no degree restriction.
4. The coefficient reduction f-bar in (A/I)[T]:
   `f.map (Ideal.Quotient.mk I)`. Verdict: exact; `Ideal.Quotient.mk` is the
   canonical coefficient ring map (Ideal/Quotient/Defs.lean:83).
5. Specified monic g₀,h₀ in (A/I)[T]: `(g₀ h₀ : (A ⧸ I)[X])`,
   `(hg₀ : g₀.Monic) (hh₀ : h₀.Monic)`. Verdict: exact.
6. The factors generate the unit ideal: `(hcoprime : IsCoprime g₀ h₀)`.
   Verdict: exact. Read Coprime/Basic.lean:45: it means existence of a,b with
   a*g₀+b*h₀=1, equivalently generation of the unit ideal, even for zero rings.
7. f-bar=g₀h₀: `(hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀)`.
   Verdict: exact, with the same factor order.
8. B=A[T]/(f): `AdjoinRoot f`. Verdict: exact; read AdjoinRoot.lean:69–71,
   defining the quotient by `Ideal.span {f}`, rather than an abstract algebra
   with an extra freeness assumption.
9. B/IB identified with the reduced polynomial quotient, and e-bar specified
   by residues (1,0): rendered directly by the two canonical `AdjoinRoot.map`
   conditions `he₁` and `he₀`. Verdict: exact. Read AdjoinRoot.lean:383–395:
   these maps reduce coefficients and send the class of X to the class of X.
   Their kernels contain IB, and on B/IB they are precisely the projections
   of the polynomial CRT map. Coprimeness makes that CRT map injective and
   surjective, so both residues are equivalent to equality of the reduction
   with the unique specified e-bar; no independent choice is discarded.
   The transported `dvd_mul_right g₀ h₀` and `dvd_mul_left h₀ g₀` give exactly
   g₀ and h₀ dividing f-bar, without another hypothesis.
10. A given idempotent e in B lifting e-bar: `(e : AdjoinRoot f)` and
    `(he : IsIdempotentElem e)`, together with `he₁` and `he₀` above.
    Verdict: exact. Read Algebra/Group/Idempotent.lean:38: e*e=e.
11. Exist monic g,h in A[T]: `∃ g h : A[X], g.Monic ∧ h.Monic ∧ ...`.
    Verdict: exact; witnesses follow all the supplied data and hypotheses.
12. f=gh: the third conjunct `f = g * h`. Verdict: exact.
13. g reduces to g₀ and h reduces to h₀: the last two conjuncts
    `g.map (Ideal.Quotient.mk I) = g₀` and
    `h.map (Ideal.Quotient.mk I) = h₀`. Verdict: exact, with correct orientation.

Edge cases: no Nontrivial, domain, field, local, Henselian, Noetherian, or
finiteness instance appears. A=0 is admitted: all polynomials and residue
classes coincide, and monicity is leadingCoeff=1=0. Degree-zero factors (1)
are admitted: AdjoinRoot 1 is the zero ring and the corresponding residue
condition holds there. Both f=1 and g₀=h₀=1 are admitted. I=0 is admitted;
I=top with hI can occur only in the zero-ring case, which is admitted. e=0
and e=1 are not excluded. Arbitrary characteristics and ring universes are
covered. Empty index sets and empty schemes are not objects in this statement;
the analogous empty spectrum of the zero ring is covered. There is no n binder
whose n=0 case could be excluded, nor an independent test-object universe.

Independent searches, with different wording from the worker:

- LeanFinder via msearch: "Lift relatively prime monic polynomial factors from
  a decomposition of the quotient algebra into two direct summands": eight
  hits in UniversalFactorizationRing. Read the closest declaration,
  UniversalCoprimeFactorizationRing.homEquiv (lines 588–594): it represents
  already-given factorizations by algebra maps into a universal ring; it does
  not obtain factorization from a lifted quotient idempotent.
- Loogle via msearch: `IsIdempotentElem, AdjoinRoot`: zero hits.
- LeanSearch via msearch: "A monic polynomial has a factorization lifting
  coprime factors when a quotient ring idempotent lifts": service unavailable
  (Internal Server Error), recorded without a mathematical verdict.
- Mathlib grep via msearch:
  `AdjoinRoot.*(factor|IsIdempotentElem)|IsIdempotentElem.*(monic|factorization)|factorization.*IsIdempotentElem`:
  only five SplittingField/Construction hits, about removing a factor over
  a field extension; none is the statement reviewed here.
- Direct rg in Mathlib/RingTheory, WeilConjectures, and lean/Sheaf with
  idempotent/factor/monic/AdjoinRoot combinations found only unrelated
  Artin–Schreier image factorizations, Henselian product decompositions,
  and étale section-lifting docstrings. Exact declaration and node-id search
  in WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json found nothing.

H4–H9: all notions come from Mathlib; no private or hollow definitions. The
only theorem has proof `by sorry`, with nothing proved in this stage. All five
node proof steps are present in its docstring: quotient/CRT; idempotent splitting
and reduction; projective locally constant ranks and the Jacobson argument;
characteristic polynomials and their product; base change and reductions.
The supporting node names, zero-ring exception, source, and blueprint tag are
present. The namespace and topic path follow the contract; all lines are at
most 100 characters. Checked that the recorded lean.statement equals the
file's signature verbatim, and every variable and universe is bound.

Validation: independent server single-file compile using scompile.py returned
exit code 0 in 1.4 seconds, with no errors or warnings. The delivery dry-run
preflight is run next and must print OK before pushing.
