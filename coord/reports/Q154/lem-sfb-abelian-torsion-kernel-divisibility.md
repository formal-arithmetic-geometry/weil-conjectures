## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.TorsionKernelDivisibility` states
`AlgebraicGeometry.existsUnique_factor_npow_of_kills_torsion`. Its sole theorem has
proof `sorry`; there are no definitions or other postponed statements. The natural-language
statement, dependency lists, and accepted proof of the node are unchanged. No new nodes,
dependency repairs, or statement corrections are needed.

Hypotheses and clauses, matched individually:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
  The statement requires an algebraically closed field itself, rather than an extension
  or a choice of algebraic closure, so the existing `IsAlgClosed` notion is used.
- The two varieties are `(A B : Over (Spec (.of k)))` with `[GrpObj A] [GrpObj B]`
  and `[IsAbelianVariety A] [IsAbelianVariety B]`. The recorded abelian-variety
  predicate supplies properness, smoothness and connectedness; its docstring explicitly
  requires the separate group-object instance, supplied here for both objects.
- The positive integer is `(n : ℕ) (hn : 1 ≤ n)`. Positive integers and natural numbers
  at least one are the same indexing range; negative integers and zero are not included
  in the node. Invertibility in the field is exactly `(hnk : IsUnit (n : k))`.
- Multiplication `[n]_A` is `𝟙 A ^ n`, precisely the upstream convention used by
  `torsionSubgroupScheme A n = GrpObj.ker (𝟙 A ^ n)`.
- The morphism `(f : A ⟶ B) [IsMonHom f]` is a homomorphism over the same field.
  The `Over` morphism includes commutation with structure maps; `IsMonHom` is the
  recorded group-scheme homomorphism notion, with inverse preservation automatic.
- A rational point is `x : 𝟙_ (Over (Spec (.of k))) ⟶ A`. The monoidal unit is the
  terminal object of the slice, representing `Spec k` over itself. Its group identity
  is `1`, the zero point in the node's additive convention. Thus membership in
  `A[n](k)` is exactly `x ≫ (𝟙 A ^ n) = 1`. This uses only rational points, and does
  not replace the hypothesis by a condition on the entire kernel scheme or on all
  extension-field points.
- The hypothesis `hf` says for every such `x`, that membership implies `x ≫ f = 1`,
  exactly the specified vanishing on every torsion rational point.
- `∃ g : A ⟶ B, IsMonHom g ∧ ...` supplies a group-scheme homomorphism over `k`.
- `f = (𝟙 A ^ n) ≫ g` is exactly `f = g ∘ [n]_A`, since categorical composition
  is written in diagrammatic order.
- `f = g ^ n` is the same factorization as divisibility in the homomorphism group.
  Powers in this Hom group use pointwise multiplication in the target, which is
  pointwise addition in the node's convention. The identity
  `MonObj.pow_comp (𝟙 A) n g`, with the homomorphism instance furnished by the
  preceding conjunct, identifies `(𝟙 A ^ n) ≫ g` with `g ^ n`. Consequently this
  conjunct states the node's equivalent description without an extra assumption.
- The final `∀ g' : A ⟶ B, IsMonHom g' → f = (𝟙 A ^ n) ≫ g' → g' = g` gives
  uniqueness among ALL group-scheme homomorphisms with the required factorization.
  In particular uniqueness does not require a competing map to come supplied with
  its scalar-multiple equality as well. The existential and this clause are the
  expanded unique-existence assertion.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs, for def-weil-field.
- `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic, for the algebraically closed
  part of def-weil-algebraic-closure. Its signature and docstring explicitly identify
  the root formulation with splitting of every polynomial.
- `AlgebraicGeometry.IsAbelianVariety`,
  WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs, for def-sc-abelian-variety.
- `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp, and
  `CategoryTheory.IsMonHom`, the inherited monoidal interface, for def-sc-group-scheme.
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs documents their precise slice
  specialization, including the Hom group convention.
- `AlgebraicGeometry.torsionSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, for def-sc-mult-n; its definition
  uses exactly the multiplication map appearing in the statement. The equivalent
  point-based kernel condition avoids creating another torsion predicate.

Every stated proof dependency has its module imported. Plain proof imports are
Mathlib.AlgebraicGeometry.Morphisms.Finite (def-weil-finite-integral-morphism),
Mathlib.AlgebraicGeometry.Sites.Fpqc (def-weil-pbc-fpqc-covering and the Mathlib match
for lem-weil-pbc-fpqc-representable-descent), Mathlib.CategoryTheory.Sites.Precoverage
(the Mathlib match for lem-galois-fpqc-covering-base-change), and the upstream
AbelianVariety.Basic, AbelianVariety.Isogeny and AbelianVariety.Torsion modules
(lem-sc-av-commutative, lem-sc-isogeny-facts and lem-sc-mult-n-etale-kernel).
The public GroupScheme.Defs import also supplies lem-sc-finite-etale-algebra-criterion.
The theorem docstring carries all seven steps of the accepted proof, including the
finite-etale justification for detecting the kernel map on rational points, the
kernel-pair maps, the two separate fpqc cancellations, and the scalar interpretation.

Edge cases checked before writing:

- `n = 1`: the hypothesis concerns only the identity point, and the unique map is `f`.
- `n = 0`: deliberately excluded by the node and by `hn`.
- In positive characteristic, multiples of that characteristic are excluded exactly
  by `hnk`; in characteristic zero every positive integer is invertible.
- Zero-dimensional abelian varieties are included. No dimension or nontriviality
  assumption is present, and the forward etaleness assertion used in the proof
  holds for the trivial abelian variety.
- The zero homomorphism is included; its unique factor is the zero homomorphism.
- The empty scheme cannot be an abelian variety with this group structure; the group
  identity gives a rational point. No extra nonemptiness hypothesis was introduced.
- The field and schemes have the standard common ambient universe `u` required by
  `Over (Spec (.of k))`. No test objects are restricted by a separate smaller
  universe, and no dimension, separability or characteristic restriction is added.

Searches made on 2026-10-24:

- `msearch.py ... leanfinder` with query "A homomorphism of abelian varieties killing
  every n torsion point factors uniquely through multiplication by n": 8 hits,
  including `ModN.liftEquiv`, `ZMod.lift`, `ModN.liftEquiv'`,
  `addMonoidHomOfForallMemZMultiples`, `QuotientAddGroup.homQuotientZSMulOfHom`,
  `AddMonoidHom.map_addCyclic`, `QuotientGroup.homQuotientZPowOfHom`, and
  `QuotientAddGroup.homQuotientZSMulOfHom_comp`. These concern abstract groups or
  quotient modules and do not give descent of an algebraic group-scheme morphism.
- `msearch.py ... loogle` with query `"AlgebraicGeometry", "torsion"`: no hits.
- `msearch.py ... grep` with query `torsion.*factor|factor.*torsion|AbelianVariety`
  under `AlgebraicGeometry`: only the comment about the 2-torsion discriminant in
  Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean, not this statement.
- `rg` in both project source roots for torsion-factor/divisibility patterns and
  the item id: unrelated torsion statements, no matching theorem. A more focused
  read/search of the upstream AbelianVariety directory found divisibility of
  POINTS, not divisibility of algebraic homomorphisms killing a kernel.
- A name search for `existsUnique_factor_npow_of_kills_torsion` found no pre-existing
  declaration in Mathlib, either source root, or the upstream-name registry.

Source reading: opened the supplied Milne PDF with pdftotext, reading Remarks
8.11(f), 8.12, Lemma 10.16 and its use in Proposition 14.4(b). The quotient universal
property and its application to a homomorphism vanishing on torsion are exactly the
source argument. No statement fault or disputed assertion was found.

Validation: the prescribed scompile.py compiled the module in sandbox mode and under
its intended library module name, both cleanly (1.8 seconds each). No warnings were
reported. The report and node signature were checked against the actual file.

## Second reading by Q154

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
