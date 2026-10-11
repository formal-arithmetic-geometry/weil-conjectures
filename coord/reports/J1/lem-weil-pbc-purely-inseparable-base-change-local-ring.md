## Worker report

The module `Sheaf.RingTheory.PurelyInseparableBaseChangeLocalRing` states
`Algebra.TensorProduct.purelyInseparable_baseChange_localRing`, with `sorry` and no proved
auxiliary declarations. The node is unchanged except for `lean`. There are no new nodes,
dependency replacements, statement corrections or disputed statements.

Hypothesis and clause correspondence:

- The fields are `(k : Type u)` and `(k' : Type v)` with `[Field k] [Field k']`.
  `[Algebra k k']` gives the specified extension map. Its finiteness and pure
  inseparability are `[Module.Finite k k'] [IsPurelyInseparable k k']`.
  The degree d is written throughout as `Module.finrank k k'`.
- `(A : Type w) [CommRing A] [Algebra k A] [IsLocalRing A] [IsNoetherianRing A]`
  renders the Noetherian local k-algebra. Its maximal ideal is
  `IsLocalRing.maximalIdeal A`, and K is `IsLocalRing.ResidueField A`, definitionally
  the quotient by that maximal ideal. All universes are explicit and unrestricted.
- A' is the literal `A ⊗[k] k'`, with the standard left-factor A-algebra structure.
  The structure map is `algebraMap A (A ⊗[k] k')`, i.e. a maps to a tensor 1.
- Clause (1): `Nonempty (Module.Basis (Fin (Module.finrank k k')) A (A ⊗[k] k'))`
  renders a free basis of rank d. `Module.Free`, `Module.Finite`, `RingHom.Flat`
  of that algebra map, and `IsNoetherianRing` state each remaining clause explicitly.
- Clause (2): `IsLocalRing (A ⊗[k] k')` states locality. The existential ideal m'
  is maximal (`m'.IsMaximal`) and all maximal ideals equal it. For every prime P,
  the displayed equivalence says exactly that P contains the mapped maximal ideal
  mA' if and only if P = m'. In particular this states mA' is contained in m'.
- Clause (3): m' maximal makes `(A ⊗[k] k') ⧸ m'` a field (Mathlib
  `Ideal.Quotient.field`). The existential ring map f from K to this quotient is
  tied to A by `f (IsLocalRing.residue A a) = Ideal.Quotient.mk m' (algebraMap A A' a)`.
  Surjectivity of A to K makes f unique. `@Module.Finite ... f.toAlgebra.toModule`
  states finite dimension for this canonical K-action, not finiteness of the
  underlying set. Injectivity of f follows from its field domain and nonzero field
  codomain, so it is precisely a finite field extension.
- The existential ring equivalence e has source A'/mA' and target K tensor k'. Its
  equation on every pure tensor is the node's exact formula. At x = 1 it states
  compatibility with the maps from A. The next equality gives K-dimension d on
  K tensor k'. The last equality gives dimension d on the actual quotient, for
  the K-action transported via e.symm from the canonical K-algebra target. The
  formula and surjectivity of A to K show this action is the canonical quotient
  K-action, so no arbitrary or independent scalar structure is supplied.

Dependency declarations used (the recorded Mathlib leaves are usable directly):

- `def-weil-pbc-finite-purely-inseparable-extension`: `IsPurelyInseparable` and
  `Module.Finite`, `Mathlib.FieldTheory.PurelyInseparable.Basic`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs` (available
  transitively); with field instances it is the node's field extension.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`.
- `def-weil-pbc-free-module`: `Module.Free` and `Module.Basis`,
  `Mathlib.LinearAlgebra.FreeModule.Basic`.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`.
- `def-weil-pbc-flat-ring-map`: `RingHom.Flat`,
  `Mathlib.RingTheory.RingHom.Flat`.

Each recorded declaration's definition and docstring was read in the pinned Mathlib.
Residue quotients use `Mathlib.RingTheory.LocalRing.ResidueField.Basic`; all notions
are existing Mathlib definitions, with no private replacement.

Edge cases checked: characteristic zero and the identity extension are included;
the identity extension gives d = 1 and A' is A. Nontrivial purely inseparable extensions
in characteristic p are included without reducedness assumptions: the closed fibre may
have nonzero nilpotents, so the statement asserts a unique prime and not that the
closed fibre is a field. A may itself be a field. The zero ring is excluded by the
standard local-ring instance. A field extension has positive degree; no extra positive
rank hypothesis was added. The basis index `Fin d` includes d = 0 syntactically but
finiteness of an extension of fields makes that value impossible. No arbitrary test
universe or auxiliary independent scalar action is used.

Source read: the local copy of `literature/stacks-project/more-algebra.tex` is absent
on this machine, so Stacks https://stacks.math.columbia.edu/tag/07E5 was opened.
Its proof of (3) => (1) uses this local ring and finite flat base change. The six-step
agent proof in the node is rendered step by step in the declaration docstring.

Searches performed for an existing whole statement:

- `msearch.py leansearch`: "The tensor product of a Noetherian local algebra with a
  finite purely inseparable field extension is finite free local and its closed fibre
  is the tensor product of the residue field". Service unavailable (Internal Server
  Error); no verdict inferred from this unavailable search.
- `msearch.py leanfinder`: "A Noetherian local k-algebra tensor a finite purely
  inseparable field extension is finite free local with closed fibre the tensor of its
  residue field". Eight results, including `Algebra.TensorProduct.isField_of_isAlgebraic`,
  geometric reducedness, quasi-finite base change and finite residue fields of formally
  unramified maps. None is the whole statement or its locality assertion.
- `msearch.py loogle`: "IsPurelyInseparable, IsLocalRing". Zero hits.
- `msearch.py grep`: "isLocalRing.*[Tt]ensor|IsLocalRing.*[Tt]ensor|purelyInseparable_baseChange_localRing".
  Nine Mathlib hits, mostly imports/open commands and local module tensor-product
  results; no matching packaged statement.
- `rg` of `WeilConjectures/` and `lean/Sheaf` for pure inseparability, tensor locality
  and the proposed full name: related field/geometric-regularity statements and
  references in proof docstrings, but no existing declaration of this statement.
- `rg` for the node id and proposed name in `WeilConjectures/`,
  `dag/lean_names_upstream.json` and `lean/Sheaf`: only two proof-docstring references
  in the project, no upstream declaration or duplicate full name.

Server compilation of the completed signature succeeds with no errors or warnings.
The independent second reader will add their own second-reading section.

## Second reading by J1

I read the node statement, its Stacks source place (More on Algebra, proof of
Proposition 07E5, (3) => (1), lines 8716--8750), and the complete Lean
declaration. The node introduces a field `k`, a finite purely inseparable field
extension `k'/k` of degree `d`, and a Noetherian local `k`-algebra `A` with
maximal ideal `m` and residue field `K`; it sets `A' = A ⊗[k] k'`, with the
left-factor `A`-algebra structure. In Lean these are `(k : Type u)`,
`(k' : Type v)`, `(A : Type w)`, `[Field k] [Field k'] [CommRing A]`,
`[Algebra k k'] [Algebra k A]`, `[IsPurelyInseparable k k']`,
`[Module.Finite k k']`, `[IsLocalRing A]`, and `[IsNoetherianRing A]`;
`A ⊗[k] k'` and `algebraMap A (A ⊗[k] k')` render `A'` and its structure map,
and `Module.finrank k k'` renders `d`. All universes are explicit.

The three conclusion clauses match as follows. Clause (1) is the conjunction
of a `Fin (Module.finrank k k')` basis, `Module.Free`, `Module.Finite`,
`RingHom.Flat`, and `IsNoetherianRing (A ⊗[k] k')`. Clause (2) is
`IsLocalRing (A ⊗[k] k')` together with an ideal `m'` that is maximal and for
every prime `P` satisfies
`Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A) ≤ P ↔ P = m'`.
This is exactly that `m'` is the only prime containing `mA'`. Clause (3) gives
the residue-field map `f : K →+* A'/m'` and finite `Module.Finite` structure,
then the ring equivalence `e : A'/mA' ≃+* K ⊗[k] k'`, its pure-tensor formula,
and the two dimension equalities, including dimension `d` for the quotient with
the transported `K`-action. These render the finite field extension, the stated
closed-fibre isomorphism compatible with `A`, and its `K`-dimension `d`.

The first reading had one mismatch: it added the conjunct
`∀ n, n.IsMaximal → n = m'`, asserting uniqueness of all maximal ideals in
addition to the node's stated uniqueness of primes containing `mA'`. Although
redundant given locality, it was an extra conclusion. I removed that conjunct
from the Lean theorem and synchronized the node's `lean.statement`; no other
clause or hypothesis changed. The source does not state this extra conjunct.

Edge cases remain covered: identity extensions and characteristic zero, positive
characteristic purely inseparable extensions with nilpotent closed-fibre
elements, `A` a field, and all allowed universes. The zero ring is excluded by
the local-ring field assumptions; `Fin (Module.finrank k k')` is retained
without an added positivity hypothesis. Searches recorded in the worker report
were re-read: LeanSearch was unavailable, LeanFinder/Loogle and grep found no
whole statement or duplicate declaration in Mathlib, `WeilConjectures`, or
`lean/Sheaf`.
