## Worker report

Item: lem-sfb-augmented-etale-associated-graded. Group: Q40. Stage: 2.
Date: 2026-10-22.

The module `Sheaf.RingTheory.FormallyEtaleAssociatedGraded` states Stacks
0H1D and the node's canonical-map compatibility clauses. Its three helper
definitions have real data: `Ideal.powerQuotientMap` specializes Mathlib's
`Ideal.quotientMap` to powers, `Ideal.associatedGradedPieceMap` restricts the
given ring homomorphism and applies Mathlib's semilinear `Submodule.mapQ`,
and `Ideal.associatedGradedMap` takes their direct sum with `DirectSum.map`.
There is no choice of an unspecified map, new associated-graded ring,
postponed definition data, or additional definition node. Each helper belongs
to the canonical maps explicitly named in this node and is recorded in
`lean.declarations` under the human's missing-helper authorization.

The primary declaration is
`Ideal.formallyEtale_powerQuotient_associatedGraded`. All eight theorem
proofs are `sorry`, including the compatibility clauses and the étale
special case. Their docstrings give the source and complete proofs.

### Hypothesis and clause correspondence

1. The commutative rings A and C are `{A : Type u} {C : Type v}` with
   `[CommRing A] [CommRing C]`; the ring homomorphism is `f : A →+* C`.
   Their universes are independent. The ideal is `J : Ideal C`.
2. The composite A → C/J is `(Ideal.Quotient.mk J).comp f`; the source's
   surjectivity hypothesis is exactly `hsurj : Function.Surjective ...`.
3. The source defines I to be its kernel. The theorem substitutes
   `J.comap f` for this determined ideal everywhere. For every a,
   a belongs to that ideal iff f(a) belongs to J iff its image in C/J
   is zero, so this introduces no new assumption or replacement ideal.
4. Formal étaleness is
   `hform : @Algebra.FormallyEtale A C _ _ f.toAlgebra`.
   The `f.toAlgebra` argument ties the algebra structure to this very f.
   Mathlib's `Algebra.FormallyEtale.iff_comp_bijective` says precisely
   that reduction on algebra homomorphisms through every square-zero
   ideal is bijective. Its test-algebra universe is `max u v`, and
   `comp_bijective` supplies lifting into any universe. No finite
   presentation assumption has been introduced.
5. For every integer n ≥ 1 the node asserts an isomorphism of quotient
   rings. `∀ n : ℕ, 1 ≤ n → Function.Bijective
   (powerQuotientMap f (J.comap f) J le_rfl n)` states this for exactly
   the positive integers. The map is a bundled ring homomorphism,
   so its bijectivity is exactly the claimed ring isomorphism.
6. Its formula [a] ↦ [f(a)] is the defining formula of
   `Ideal.quotientMap`. Preservation of powers uses the existing
   `pow_le_pow_left'` and `Ideal.le_comap_pow`; no missing proof
   or hollow hypothesis is used to define the map.
7. The associated graded is exactly the dependency's
   `Ideal.associatedGraded`, with pieces `Ideal.associatedGradedPiece`.
   The conclusion supplies
   `e : associatedGraded (J.comap f) ≃+* associatedGraded J` and the
   equality `e.toAddMonoidHom = associatedGradedMap ...`.
   This pins the equivalence to the actual canonical map, including
   its values in degree zero. It is not a bare existence of an
   unrelated ring equivalence.
8. Grading is retained because the actual additive map is
   `DirectSum.map` of the degree n maps. Each piece map is
   `Submodule.mapQ` of the restriction of `f.toSemilinearMap`.
   Thus a homogeneous representative a in I^n is sent to the class
   of f(a) in J^n/J^(n+1), in the same degree. The direct sum has
   finite support by its existing definition. A bijective direct
   sum of these degree-preserving maps has degree-preserving inverse.
9. The graded A/I = C/J algebra assertion is expressed without a
   second scalar structure: for every a and x,
   `e ((Ideal.Quotient.mk (J.comap f) a) • x) =
   (Ideal.Quotient.mk J (f a)) • e x`.
   Both scalar actions are the dependency's `associatedGradedAlgebra`.
   The coefficient map in this formula is exactly the canonical
   level-one quotient isomorphism from the first conjunct. Every
   coefficient has such a representative, so this is full linearity
   over the identified coefficient rings, not just A-linearity.
10. `powerQuotientMap_naturality` and
    `associatedGradedMap_naturality` state commutativity for every
    square of ring maps with `g.comp f = f'.comp aMap`, and precisely
    the four ideal-preservation inequalities needed to form those
    maps. The four rings have independent universes. These equations
    are asserted for the actual canonical maps. Naturality needs
    neither formal étaleness nor surjectivity and is the stronger
    elementary compatibility of the constructions themselves.
11. `powerQuotientMap_comp`, `associatedGradedMap_comp`, and the two
    `_id` theorems give composition and identity compatibility on
    those same maps. Ideal preservation by the composite is derived
    from the two given preservation inequalities rather than added
    as a redundant hypothesis.
12. The parenthetical scheme case is
    `AlgebraicGeometry.formallyEtale_of_etale_spec`: the hypothesis
    is `Etale (Spec.map (CommRingCat.ofHom f))`, and the conclusion
    is exactly the main theorem's formal-étaleness hypothesis for f.
    As in Mathlib's scheme category, the rings in this scheme-only
    corollary inhabit a common arbitrary universe; the main ring
    theorem imposes no common-universe restriction.
13. There is no Noetherianity, finite generation, finite presentation,
    nonzero-ring, proper-ideal, or `J = I*C` assumption. No statement
    correction was needed. No `STATEMENT-DISPUTED` flag remains.

### Dependency declarations read and used

* `def-weil-etale-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`. Its affine-local ring-map definition
  is used in the parenthetical special case.
* `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
  They are publicly available through the étale import.
* `def-weil-pbc-algebra-hom-quotient` is a Mathlib leaf with no `lean`
  record. Its `mathlib_match` is used directly: `AlgHom` in
  `Mathlib.Algebra.Algebra.Hom`, and `Ideal.Quotient.algebra`,
  `Ideal.Quotient.mkₐ`, `Ideal.quotientMap` in
  `Mathlib.RingTheory.Ideal.Quotient.Operations`, along with the
  existing operations and powers of ideals. Quotient operations
  are publicly imported by the associated-graded dependency.
* `def-weil-pbc-associated-graded-ring`:
  `WeilConjectures.RingTheory.AssociatedGradedRing`,
  `Ideal.associatedGradedPiece`, `Ideal.associatedGraded`,
  `Ideal.associatedGradedAlgebra` and the ring and homogeneous-product
  structure recorded in that node. The complete module was read.
* The recorded proof-dependency modules are imported without
  `public`: `WeilConjectures.AlgebraicGeometry.FormallySmooth`,
  `WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale`,
  `Sheaf.AlgebraicGeometry.AffineFormallySmooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`, and
  `Mathlib.RingTheory.Unramified.Basic`.
  Their relevant declarations are respectively
  `AlgebraicGeometry.FormallySmooth`,
  `AlgebraicGeometry.flat_unramified_formally_etale`,
  `AlgebraicGeometry.formallySmooth_spec_iff_ringHom_formallySmooth`,
  `AlgebraicGeometry.HasRingHomProperty.Spec_iff`, and
  `Algebra.FormallyUnramified.iff_comp_injective` / `comp_injective`.
  The associated-graded ring-structure proof dependency shares the
  already public associated-graded module.

### Source and edge cases

Read `literature/stacks-project/algebra.tex`, the complete statement
and proof of `lemma-formally-etale-lift-infinitesimal` (Tag 0H1D),
and the statement and proof of `lemma-formally-etale-etale` (Tag 00UR).
The tag-label identifications were checked in `tags/tags`.

* n = 1 is the quotient by the actual kernel; the formal-étaleness
  induction begins there. n = 0 is excluded only from the positive
  quotient assertion. Graded degree zero is included by the direct
  sum construction and is the level-one quotient map.
* J = top is allowed: both quotient systems and both graded rings
  are zero. Zero rings are allowed throughout; no `Nontrivial`
  instance appears.
* J = bottom is allowed. A surjective formally étale map can have
  nonzero idempotent kernel, so the theorem does not incorrectly
  demand that the original f be an isomorphism.
* The diagonal k → k × k with J = 0 × k has I = 0 but J ≠ I*C;
  its quotient and graded maps are isomorphisms. The statement
  correctly includes this example.
* The identity map with any ideal has identity comparison maps.
* k → k[t], J = (t), is formally smooth but not formally étale;
  the higher quotient conclusion fails. This confirms that the
  uniqueness part of the lifting hypothesis must be retained.
* Naturality and composition also cover identity comparison maps,
  zero rings, and arbitrary ideal-preserving maps. The piece and
  direct sum constructions do not assume positive degree.

### Searches

The following calls used the prescribed `batch2/msearch.py` wrapper
with group Q40 and this exact item id:

* `leanfinder`: "A formally etale ring map which induces an isomorphism
  modulo ideals induces isomorphisms modulo all powers and on associated
  graded rings". Eight results included
  `Algebra.FormallyEtale.comp_bijective`, `iff_comp_bijective`,
  localization results, and standard étale lifting. None stated 0H1D.
* `loogle`: `"Algebra.FormallyEtale", "quotient"`. One result was
  `Algebra.FormallyEtale.instIsSeparableQuotientIdealOfEssFiniteTypeOfIsPrime`,
  about residue-field separability, not this result.
* `grep`, Mathlib `RingTheory`:
  `FormallyEtale.*[Qq]uotient|[Ee]tale.*[Gg]raded|associatedGraded.*[Mm]ap`.
  Zero results.
* `leansearch`: "A formally etale ring homomorphism inducing an
  isomorphism modulo an ideal induces isomorphisms modulo all ideal
  powers and of associated graded rings". Eight results included
  `RingHom.FormallyEtale`, `RingHom.Etale`,
  `Algebra.FormallyEtale`, and differential comparison results.
  None stated this result.

Direct `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for
associated-graded maps, equivalences and étale quotients found the
recorded associated-graded construction, specific Rees and regular
sequence maps, conormal graded-algebra stalk comparisons, and
unrelated sheaf quotients. None was the general formally étale
comparison. Searching the exact item id in both library roots
found no existing module. A final search of both library roots and
`dag/lean_names_upstream.json` for all the new declaration names
found no collision.

### Assignment history and validation

The previous worker's claimed completed-node blocker was incorrect:
ledger line 24657 records NN's stage-1 split review, and the node's
`reviewed` record confirms that fact. It had no `lean` or
`reviewed_lean` record. Stage 2 does not re-split the node; this
delivery changes only its `lean` field.

All variables and universes are explicitly bound, with
`set_option autoImplicit false`. The module has no file-local
notation, local instance, private helper, or theorem proof other
than `sorry`. The helpers reuse existing proofs for preservation
of ideal powers and well-defined maps; no proof used by a definition
is left as `sorry`.

The final module passed `batch2/scompile.py Q40
lem-sfb-augmented-etale-associated-graded <module path>` in both
sandbox and library modes (3.5 s each). No compiler errors or
unexpected warnings were emitted. Delivery preflight is run using
the prescribed `deliver2.py --no-push` wrapper.

## Second reading by Q40

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
