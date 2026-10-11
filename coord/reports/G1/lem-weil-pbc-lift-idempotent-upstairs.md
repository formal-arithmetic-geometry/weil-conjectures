## Worker report

The module states the lifting theorem in `AlgebraicGeometry.exists_etale_lift_isIdempotentElem`.
A commutative ring `A`, ideal `I`, commutative `A`-algebra `B` integral over `A`, and an
idempotent of `B/(I B)` are given. The existential `A' : CommRingCat` and map `g` render
the required ring map and its étale spectrum map. The `letI` installs the induced algebra
structure. The ring equivalence `α` renders `A/I ≅ A'/IA'`; `e'` and
`IsIdempotentElem e'` render the lifted idempotent; `β` is the tensor quotient
identification and the final equality is the explicit lifting condition.

The statement dependency is Mathlib's `AlgebraicGeometry.Etale` from
`Mathlib.AlgebraicGeometry.Morphisms.Etale`.

Edge cases checked: `I = ⊥`, `I = ⊤`, zero rings, and idempotents `0` and `1` are all
allowed by the unrestricted ideal and ring binders; no finiteness or nonzero hypotheses
were added. The universe is shared (`Type u`) and the étale algebra may be any
`CommRingCat` object.

Searches: the node's recorded LeanSearch, LeanFinder, Loogle, and Mathlib grep searches
found no statement of Stacks Tag 07M4; the project search found no existing declaration.

## Earlier second reading (a previous round; superseded)

Reading the node and file clause by clause, `CommRing A`, `CommRing B`, integrality,
ideal, and idempotent hypotheses are present. The `CommRingCat` existential with `g`
and `Etale (Spec.map g)` gives the étale base change. `α` gives the quotient isomorphism,
and `e'`, its idempotence, `β`, and the final equation give the lifting clause. The
Lean formulation uses the canonical `Algebra A B` map for `IB` and an induced algebra
structure on `A'`; these are the standard Mathlib encodings of the ring maps.

## Second reading by G1

Read the sandbox node, the module, the sole statement dependency
`def-weil-etale-morphism`, and its recorded Mathlib declaration and equivalence
`Etale.iff_flat_and_formallyUnramified`. Read the source in the local Stacks mirror
`/home/ubuntu/c1-stacks-review/more-algebra.tex`, section Lifting, including its
standing discussion of quotient-preserving étale extensions and the complete
`lemma-lift-idempotent-upstairs` statement and proof (Tag 07M4).
`conventions.tex` specifies that rings are commutative with 1. This section imposes
no Noetherian, nonzero, finite-module, characteristic, or proper-ideal assumption.

The node's objects, hypotheses, and conclusions, matched individually:

| Node item | Lean rendering and verdict |
| --- | --- |
| A commutative ring A | `{A : Type u} [CommRing A]`: exact, including the zero ring. |
| An ideal I of A | `(I : Ideal A)`: exact, with no restriction. |
| A commutative ring B and ring map A → B | `{B : Type v} [CommRing B] [Algebra A B]` with `algebraMap A B`: exact. For commutative rings every unital ring map gives this algebra structure; no additional algebra condition is introduced. |
| B integral over A | `[Algebra.IsIntegral A B]`: exact; no module finiteness added. |
| The extended ideal IB and its quotient | `I.map (algebraMap A B)` and `B ⧸ I.map (algebraMap A B)`: exact. |
| An idempotent ebar in B/IB | `(ebar : B ⧸ I.map (algebraMap A B)) (hebar : IsIdempotentElem ebar)`: exact. |
| A ring A' and ring map A → A' | `∃ (A' : CommRingCat.{u}) (g : CommRingCat.of A ⟶ A')`, followed by `letI : Algebra A A' := g.hom.toAlgebra`: exact structure map. |
| Spec A' → Spec A is étale | `Etale (Spec.map g)`: exact recorded dependency, not a new notion. |
| The induced map α : A/I → A'/IA' is an isomorphism | `∃ α : A ⧸ I ≃+* A' ⧸ I.map (algebraMap A A')` together with `∀ a : A, α (Ideal.Quotient.mk I a) = Ideal.Quotient.mk _ (algebraMap A A' a)`: exact after repair. Representatives exhaust A/I, so this fixes α to the induced quotient map. |
| An idempotent e' in B ⊗_A A' | `∃ (e' : TensorProduct A B (A' : Type u)), IsIdempotentElem e'`: exact. |
| The specified composite maps e' to ebar | `∃ β` of the displayed quotient-ring-equivalence type, the representative equation `∀ b : B, β (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (Algebra.TensorProduct.includeLeftRingHom (R := A) (B := A') b)`, and `β ebar = Ideal.Quotient.mk _ e'`: exact after repair. |

For the last row, the canonical map B/IB → (B ⊗_A A')/I(B ⊗_A A')
is induced by b ↦ b ⊗ 1. It is an isomorphism because the canonical α is
an isomorphism and tensoring identifies these quotients with B ⊗_A (A/I)
and B ⊗_A (A'/IA'), respectively. Thus the existential β is no stronger
than the node and its representative equation uniquely fixes the map. Its inverse
is the node's composite using id_B ⊗ α⁻¹. The final equation is equivalent to
that composite sending e' to ebar. The quantifier order remains given A, B, I,
ebar, then a neighbourhood and its quotient identification, then a lift. The
additional β witness is uniquely determined by the chosen neighbourhood.

Mismatches and repairs:

- H3: the first worker's α was an arbitrary ring equivalence, not constrained to
  the map induced by g. Added its equation on all representatives of A/I.
- H3: β was another arbitrary ring equivalence, with no relationship to α or g.
  Added its equation on all representatives of B/IB. The Worker report's claim
  that this was already the canonical identification was incorrect; the repaired
  signature now actually requires it.
- Universes: separated `{A : Type u}` and `{B : Type v}` and made the witness
  universe `CommRingCat.{u}` explicit. The tensor and its quotient live in
  `Type (max u v)` without excluding larger integral algebras B. A' can be chosen
  in A's universe: the source constructs a finitely presented étale algebra
  over A and a principal localization, independently of the size of B.
- H8: the original docstring compressed the proof into a summary and a list of
  dependencies. Replaced the proof plan by all eight steps of the node, each
  with its dependencies and the final identification bookkeeping.
- Updated `lean.statement` to the signature verbatim, excluding `:= by sorry`.
  No mathematical node statement or dependency list changed; no statement
  correction record, new node, or dependency module is needed.

Edge cases: I = ⊥ and I = ⊤ are included. For I = ⊤ all quotient rings
are the zero ring and their representative equations impose no spurious
nonzero condition; e' = 0 with the identity neighbourhood is admissible.
Zero A or B, empty spectra, ebar = 0 or 1, and every characteristic are included.
No index set or natural-number parameter occurs in the statement; the d ≥ 1
in the proof is a constructed annihilator exponent, not a hypothesis.
The independent universes u and v are explicitly bound and no auto-implicit
variable or independent lower test-object universe occurs.

Independent searches (recorded also by msearch in the sandbox searches.jsonl):

- LeanSearch: "An idempotent modulo an ideal in an integral algebra lifts after
  an etale base change inducing an isomorphism on the quotient of the base ring".
  Service returned Internal Server Error; unavailable, not a negative result.
- LeanFinder: "integral extension idempotent quotient ideal lifts after etale
  neighbourhood preserving closed subscheme". Eight hits, including
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` and
  `StandardEtalePair.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot`.
- Loogle: `IsIdempotentElem, Algebra.Etale`. Two hits, both the primewise
  quasi-finite splitting theorem and its auxiliary lemma.
- rg over Mathlib's Etale and Idempotents files, the complete project's
  `lean/Sheaf`, and source `WeilConjectures`, for
  `exists_etale.*Idempotent|07M4|lift.*[Ii]dempotent`; also checked the chosen
  full declaration name in these trees and `dag/lean_names_upstream.json`.
  No duplicate of this statement or declaration name was found.
- Opened the actual signature and docstring of Mathlib's Tag 00UJ theorem
  (`Etale/QuasiFinite.lean:379`) and upstream
  `Algebra.exists_etale_isIdempotentElem_forall_eq`
  (`Etale/FiniteSplitting.lean:76`). They isolate a prime/geometric point under
  finite-type or finite-module assumptions; they do not lift an arbitrary given
  idempotent modulo an arbitrary ideal preserving the entire base quotient.
  Existing henselian and nilpotent lifting statements likewise impose different
  hypotheses. None replaces this module.

H4/H5/H6/H9: all notions come from Mathlib; no definition, private copy, or hollow
data was introduced. The only theorem retains `by sorry`. The source and
blueprint tags occur in both docstrings. Imports supply the étale predicate,
tensor inclusion, and quotient algebra structures used in the signature. Lines
are within 100 characters, and declarations have no Sheaf namespace prefix.

Validation: the revised complete module compiled on the server with scompile.py,
exit code 0, in 1.8 seconds, with no errors or warnings. The signature was checked
against the node's lean.statement verbatim.
