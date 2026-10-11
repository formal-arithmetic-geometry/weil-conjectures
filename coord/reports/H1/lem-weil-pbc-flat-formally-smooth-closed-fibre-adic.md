## Worker report

The module `lean/Sheaf/RingTheory/FormallySmoothAdicOfFlatClosedFiber.lean` states
`RingHom.formallySmoothAdic_of_flat_closedFiber`, with its only proof `by sorry`.
No new definition, dependency module, statement correction or disputed statement is needed.
The declaration docstring carries all eleven proof steps from the node, including the nodes
used by each step. No mathematical result is proved in this delivery.

Clause-by-clause correspondence:

- The local homomorphism `f : (A, m_A) → (B, m_B)` is `(f : A →+* B)` with
  `[CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsLocalHom f]`.
  Mathlib's local-map condition reflects units; for local rings this is precisely preservation
  of the maximal ideals. The rings are arbitrary `A : Type u`, `B : Type v`.
- Noetherianity of both rings is `[IsNoetherianRing A] [IsNoetherianRing B]`, using the
  declaration of `def-weil-pbc-noetherian-ring`.
- The structure map for the conclusion is fixed, rather than supplied independently:
  `letI : Algebra A B := f.toAlgebra`.
- The residue field `k = A/m_A` is `A ⧸ maximalIdeal A`. No independent field or choice
  of identification is introduced.
- The fibre `Bbar = B/m_A B` is `B ⧸ I`, where
  `let I : Ideal B := Ideal.map f (maximalIdeal A)`. Ideal.map is extension of the ideal,
  including all B-linear combinations of images, not just the set-theoretic image.
- The induced k-algebra structure is the actual Mathlib construction
  `Ideal.Quotient.algebraQuotientOfLEComap`, using `Ideal.le_comap_map` to descend the
  structure map. On classes it sends the class of a to the class of f(a); there is no
  arbitrary algebra-structure binder or additional compatibility hypothesis.
- The maximal ideal `mbar = m_B/m_A B` is written as
  `Ideal.map (Ideal.Quotient.mk I) (maximalIdeal B)`.
  Since f is local, I lies in m_B; hence this extension along the surjective quotient map
  is exactly that quotient ideal and is the unique maximal ideal of the fibre.
- Flatness is `(hflat : f.Flat)`, the recorded `RingHom.Flat` definition.
- The closed-fibre hypothesis is
  `Algebra.FormallySmoothAdic (A ⧸ maximalIdeal A) (B ⧸ I)
    (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal B))`.
- The conclusion is `Algebra.FormallySmoothAdic A B (maximalIdeal B)`, with the
  A-algebra structure induced by f. The implication after the lets binds precisely the
  closed-fibre hypothesis, with no additional assumption.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing` (definition: Noetherian as
  a module over itself, equivalently every ideal finitely generated).
- `Mathlib.RingTheory.Ideal.Quotient.Operations`, `Ideal.Quotient.algebra`,
  `Ideal.Quotient.mkₐ` and `Ideal.Quotient.algebraQuotientOfLEComap`; and
  `Mathlib.Algebra.Algebra.Hom`, `AlgHom`: these are the quotient-algebra and
  algebra-homomorphism notions of `def-weil-pbc-algebra-hom-quotient`, also used inside
  the imported adic formal-smoothness definition. Powers and extensions of ideals are
  Mathlib's ideal operations. The mapped-ideal inclusion uses `Ideal.le_comap_map`.
- `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`: flatness via f.toAlgebra,
  as recorded by `def-weil-pbc-flat-ring-map`.
- `Sheaf.RingTheory.FormallySmoothAdic`, `Algebra.FormallySmoothAdic`: the full
  recorded definition of `def-weil-pbc-formally-smooth-adic` was read and imported.
  This is the square-zero lifting property restricted to maps killing a positive ideal
  power, not Mathlib's unrestricted discrete `Algebra.FormallySmooth`.

Source check: local literature/stacks-project/more-algebra.tex is not present on this
machine. Read https://stacks.math.columbia.edu/tag/07NQ instead: Proposition 15.41.5
has exactly a local homomorphism of Noetherian local rings, condition (2) flatness plus
adic formal smoothness of the special fibre, and condition (3) adic formal smoothness
of the target over the base. Its proof matches the eleven steps supplied by the node.
No source-wide hypothesis was omitted. The special fibre tensor description in the
source is canonically the quotient used by the node and this statement.

Edge cases checked before writing:

- If A is a field then m_A = 0, the quotient fibre is canonically B and the hypothesis
  is exactly the intended adic formal smoothness over A; no positive-dimension assumption.
- If B is a field then m_B = 0, and the adic condition on B is the discrete lifting
  condition. The theorem includes this case.
- Artinian and noncomplete local rings are allowed; completeness is only introduced in
  the natural-language proof, never required by the Lean statement.
- Both equal and mixed residue characteristics are allowed; no characteristic binders.
- The zero ring is excluded already by IsLocalRing, consistently with local rings having
  a proper maximal ideal in the source. A local f ensures the fibre is nonzero, so no
  extra nontriviality condition is required.
- Independent universes u and v are explicit. The fibre and residue quotient retain
  these universes, and the imported FormallySmoothAdic quantifies test rings in
  Type (max u v) for both hypothesis and conclusion; no new universe restriction.
- No finite presentation, finite type, injectivity, surjectivity or separability assumed.

Searches for an existing statement (2026-10-11):

- msearch.py leanfinder: "A flat local homomorphism of Noetherian local rings with formally
  smooth closed fibre for the maximal ideal adic topology is formally smooth adically".
  Eight hits: Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing,
  Algebra.Smooth.flat_of_isNoetherianRing, AdicCompletion.flat_of_isNoetherian,
  Algebra.Smooth.flat, two discrete formal-smoothness lifting lemmas for complete targets,
  RingHom.smooth_def, and Algebra.Smooth.formallySmooth. None states this adic implication.
- msearch.py loogle: "Algebra.FormallySmooth, RingHom.Flat". Zero hits.
- msearch.py grep in RingTheory: "formallySmooth.*(flat|fibre)|FormallySmooth.*(Flat|Residue)".
  Seventeen hits in Etale/Descent and Smooth/{Local,Flat,Quotient,Fiber}. Read the nearby
  declaration FormallySmooth.of_formallySmooth_residueField_tensor in Smooth/Fiber:
  it assumes an essentially finitely presented presentation and uses discrete formal
  smoothness, so it is not the present arbitrary-Noetherian adic statement.
- msearch.py leansearch: "flat local homomorphism Noetherian local rings formally smooth
  closed fibre adic topology". UNAVAILABLE: Internal Server Error; no verdict assigned.
  The available semantic, Loogle and source searches above were used.
- rg for FormallySmooth and closed.fibre in the project's RingTheory source and
  lean/Sheaf/RingTheory: the adic definition and unrelated statements (including flatness
  criteria and power-series smoothness); no existing statement for this node.
- rg for the exact item id throughout WeilConjectures: no match.
- rg for the proposed declaration names in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no collision.

Validation: scompile.py H1 lem-weil-pbc-flat-formally-smooth-closed-fibre-adic on this
single module compiled cleanly on the server in 1.6 seconds (exit 0), no warnings.
All variables and universes are explicitly bound. The node copy changes only `lean`.
The delivery dry run is run after this report; the second reader supplies the independent
second-reading section and delivers the item.

## Second reading by H1

I independently read the node statement, its Tag 07NQ source place, and the Lean
signature in `Sheaf.RingTheory.FormallySmoothAdicOfFlatClosedFiber`.

- Objects: the local map `f : A →+* B` with `[CommRing]`, `[IsLocalRing]`, and
  `[IsLocalHom f]` renders the local homomorphism; the independent universes `u v`
  permit all rings covered by the node.  The Noetherian hypotheses are exactly
  `[IsNoetherianRing A]` and `[IsNoetherianRing B]`.
- The `letI : Algebra A B := f.toAlgebra` is the structure map induced by `f`.
  `I := Ideal.map f (maximalIdeal A)` renders `m_A B`, and the residue field is
  `A ⧸ maximalIdeal A`.  The quotient algebra instance is precisely
  `Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map ...)`, so it is the
  induced `k`-algebra and introduces no extra compatibility data.
- The fibre is `B ⧸ I`; its maximal ideal is rendered by
  `Ideal.map (Ideal.Quotient.mk I) (maximalIdeal B)`, which is the quotient
  `m_B/m_A B` because locality gives `m_A B ≤ m_B`.
- The flatness hypothesis is exactly `hflat : f.Flat`.  The sole premise of the
  implication is `Algebra.FormallySmoothAdic (A ⧸ maximalIdeal A) (B ⧸ I)
  (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal B))`; the conclusion is exactly
  `Algebra.FormallySmoothAdic A B (maximalIdeal B)`.  Quantifier order and all
  clauses agree with the node, with no added finiteness or characteristic
  assumptions.

Edge cases checked: field A (zero maximal ideal), field B (zero target maximal
ideal), Artinian and noncomplete local rings, mixed and equal residue
characteristic, and independent universes.  The local-ring classes exclude the
zero-ring case as in the source; no positivity, finite-presentation, or
separability condition is added.  The quotient and ideal-map formulation also
covers the zero-dimensional and trivial-fibre cases allowed by the statement.

I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` with the semantic
searches recorded by the worker, exact-name and `rg` searches, and Loogle/
LeanFinder.  No existing declaration states this arbitrary-Noetherian adic
flat-closed-fibre implication; the nearby Mathlib fibre theorem is a discrete,
essentially-finitely-presented result and is not equivalent.

No mismatch was found.  I changed no Lean declaration or node statement.  The
module compiles cleanly with `scompile.py`; its only proof is the permitted
`sorry`, and all variables and universes are explicit.
