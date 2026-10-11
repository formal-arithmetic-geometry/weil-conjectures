## Worker report

The module states `Algebra.separable_residue_cotangent_injective` for a field `k`, a
commutative Noetherian local ring `R` with a `k`-algebra structure, finitely generated
residue field, and separable residue extension. The residue field is rendered by
`IsLocalRing.ResidueField R`; finite generation is the Mathlib predicate
`Algebra.FiniteType k (IsLocalRing.ResidueField R)`, and separability is
`Algebra.IsSeparableExtension k (IsLocalRing.ResidueField R)`.

The source map is rendered by `KaehlerDifferential.kerCotangentToTensor k R
(IsLocalRing.ResidueField R)`, whose domain is the cotangent quotient of the kernel of the
residue map and whose value is `1 ⊗ₜ d a`. The source cotangent space
`m/m^2` is `IsLocalRing.CotangentSpace R`; it is identified with that kernel cotangent
through `Ideal.Cotangent.equivOfEq` using `IsLocalRing.ker_residue.symm`. The conclusion
is `Function.Injective` of their composition, exactly the asserted injectivity.

Dependencies used: `Mathlib.RingTheory.Ideal.Cotangent` (`IsLocalRing.CotangentSpace`,
`Ideal.Cotangent.equivOfEq`, `IsLocalRing.ker_residue`),
`Mathlib.RingTheory.Kaehler.Basic` (`KaehlerDifferential.kerCotangentToTensor`), and
`Sheaf.FieldTheory.SeparableExtension` (`Algebra.IsSeparableExtension`). The Noetherian
notion is Mathlib `IsNoetherianRing`; field extension and Kähler differentials use their
Mathlib structures.

Edge cases checked: the local ring may be a field (then the maximal ideal and cotangent
space are zero); the residue field may be the base field; no characteristic or positivity
assumption is imposed; universes of `k` and `R` are explicit.

Searches made: `msearch.py leanfinder` for the stated cotangent injection (only formal
smoothness criteria); `msearch.py loogle` for `IsLocalRing.CotangentSpace, KaehlerDifferential`
(no direct theorem); `msearch.py grep` and `rg` through Mathlib and WeilConjectures for
cotangent/Kähler declarations (found `kerCotangentToTensor`, but no statement matching this
lemma). Thus a new module was required.

## Earlier second reading (a previous round; superseded)

The hypotheses bind exactly the field, commutative Noetherian local ring, algebra structure,
finite generation, and separability from the node. The conclusion uses the residue map's
kernel cotangent, transported from `m/m^2` by the equality of ideals, and the canonical
`a ↦ 1 ⊗ d a` map; `Function.Injective` expresses the required injectivity. No clause or
edge case is omitted.

## Second reading by G1

I independently read the sandbox node and module, all four statement-dependency
nodes and their recorded declarations, and the Stacks source. The repository's
literature directory has no algebra.tex on this machine; I read the available
Stacks checkout /home/ubuntu/c1-stacks-review/algebra.tex, lines 38680–38745,
and verified 00TU in its tags/tags. This is the stated lemma and its whole proof.
It assumes a field k, a Noetherian local ring containing k, and a finitely
 generated separable residue extension; there is no further standing smoothness,
regularity, finite-type algebra, perfection, or characteristic hypothesis.
I also read Definition 030O, lines 9915–9930, for nonalgebraic separability.

Object/hypothesis/conclusion inventory and correspondence:

1. Field k: `(k : Type u) [Field k]`. Exact; no perfection or characteristic
   restriction. Its universe is arbitrary.
2. Commutative Noetherian local ring R: `(R : Type v) [CommRing R]
   [IsLocalRing R] [IsNoetherianRing R]`. Exact. The dependency
   def-weil-pbc-noetherian-ring records Mathlib's IsNoetherianRing, which I read
   in RingTheory/Noetherian/Defs.lean:196–206: all ideals are finitely generated.
   Locality includes the nontriviality required for a residue field.
3. R is a k-algebra, with k contained in R: `[Algebra k R]`. Exact. I read the
   Algebra signature in Algebra/Algebra/Defs.lean:95, recorded by
   def-pc-field-extension. A unital map out of the field into this nontrivial
   ring is injective, so no additional embedding hypothesis is needed.
4. Maximal ideal m and residue field κ = R/m, with the composite k → R → κ:
   `IsLocalRing.maximalIdeal R` and `IsLocalRing.ResidueField R`. Exact. I read
   LocalRing/ResidueField/Basic.lean:30–61: residue is Ideal.Quotient.mk,
   its kernel is the maximal ideal, and the induced Algebra instance and scalar
   tower are the quotient instances. No independently chosen residue extension
   or compatibility assumption is introduced.
5. κ is finitely generated AS A FIELD over k: repaired to
   `(hfg : (⊤ : IntermediateField k (IsLocalRing.ResidueField R)).FG)`.
   IntermediateField/Adjoin/Defs.lean:653 defines FG by existence of a finite
   set whose FIELD adjoin equals the intermediate field. At top this is exactly
   κ = k(a₁, …, aₙ). The original `[Algebra.FiniteType k κ]` was stronger and
   excluded transcendental finitely generated fields. Verdict: now exact.
6. κ/k is separable in the nonalgebraic sense:
   `(hsep : Algebra.IsSeparableExtension k (IsLocalRing.ResidueField R))`.
   Exact. I opened Sheaf/FieldTheory/SeparableExtension.lean: the predicate is
   `∀ F : IntermediateField k κ, F.FG → IsSeparablyGenerated k F`, exactly
   Definition 030O (2). IsSeparablyGenerated uses a transcendence basis with
   Algebra.IsSeparable over its field adjoin, matching (1). This uses the
   recorded def-weil-pbc-separable-field-extension, not algebraic separability
   of κ/k or a private replacement.
7. Ω[R/k] and its universal derivation d: the target of
   `KaehlerDifferential.kerCotangentToTensor k R κ` uses Mathlib's
   KaehlerDifferential and D. Exact. I read their definitions and
   linearMapEquivDerivation in Kaehler/Basic.lean:153, 198, 327, as recorded by
   def-weil-pbc-kahler-differentials; composition with D gives the defining
   universal property for all R-modules.
8. Source m/m²: the domain of `Ideal.Cotangent.equivOfEq` is
   `(IsLocalRing.maximalIdeal R).Cotangent`, definitionally
   `IsLocalRing.CotangentSpace R`. Exact. I read Ideal/Cotangent.lean:47–80,
   273–310: Cotangent is the ideal modulo I times itself, and its quotient
   map has kernel I². The equality `IsLocalRing.ker_residue.symm` transports
   m to ker(R → κ), preserving each representative.
9. Canonical κ-linear map [a] ↦ d a ⊗ 1: the composition of this ideal-equality
   transport with `KaehlerDifferential.kerCotangentToTensor` is [a] ↦ 1 ⊗ d a.
   Exact under the canonical tensor symmetry κ ⊗[R] Ω[R/k] ≅ Ω[R/k] ⊗[R] κ.
   I read kerToTensor, kerCotangentToTensor, and the representative formula in
   Kaehler/Basic.lean:764–789 and equivOfEq_toCotangent. The map is packaged
   R-linearly; both modules are killed by m, so its R-linearity is precisely
   κ-linearity by surjectivity of the residue map. This packaging imposes no
   hypothesis or extra conclusion. The tensor-order convention is now explicit
   in the docstring.
10. Conclusion: `Function.Injective` of exactly that composition. Exact; no
    splitting, surjectivity, dimension, or regularity conclusion is asserted.
    All objects precede hypotheses, and the hypotheses precede the conclusion.

Edge cases: empty field generators give κ = k (n = 0), permitted by FG of top;
empty transcendence bases include finite separable algebraic extensions. The
case R a field gives m = 0 and a zero cotangent source, still covered. In
particular R = k(t) is a Noetherian local k-algebra with separable residue field
finitely generated as a FIELD, covered after the repair; k(t) is not a finite
 type k-algebra (Zariski's lemma), so it witnesses the old hypothesis defect.
The zero ring is excluded already by the source's local ring containing a
field, not by an added hypothesis. All characteristics and arbitrary independent
universes u and v are covered, and no index or test-object universe occurs.
Empty schemes and empty index sets do not occur in this ring-theoretic statement.

Independent searches (recorded by msearch.py in searches.jsonl):

- LeanSearch: “cotangent space of a local algebra injects into residue base
  change of differentials when the residue extension is separably generated”.
  The service returned Internal Server Error; no mathematical verdict is drawn.
- Loogle: `KaehlerDifferential.kerCotangentToTensor`. Found the canonical map,
  its exactness and representative formula, a section/retraction equivalence,
  and formal-smoothness criteria. I read Smooth/Basic.lean:276–300: their
  formally smooth SOURCE hypothesis is absent here, so no exact theorem match.
- LeanFinder: “A Noetherian local ring containing k with finitely generated
  separable residue extension has injective conormal map from its maximal ideal
  modulo its square to differential forms tensored with the residue field”.
  Returned presentation-based formal-smoothness criteria, submersive
  presentations, and finite dimensionality of the cotangent space. None states
  this injectivity result for arbitrary Noetherian local R.
- Mathlib grep: `kerCotangentToTensor.*inject|cotangent.*separab|separab.*cotangent`.
  Only the same Smooth/Basic criterion was found.
- Direct rg with the additional full theorem name and kerCotangentToTensor
  in WeilConjectures/, repository lean/Sheaf/, and dag/lean_names_upstream.json.
  The upstream Smooth/Local.lean uses that criterion for a formally smooth
  source B (read the invocation at lines 109–110); the project citer
  RegularLocalSeparableResidueSmooth.lean refers to this DAG lemma in its
  docstring, not an already existing declaration. No duplicate theorem found.

Repairs: H3 finite algebra generation replaced by finite FIELD generation,
without changing the correct node statement or its dependencies. H8 repaired:
the original theorem docstring had no proof; it now gives all five DAG steps,
including the 02HQ comparison, finite separating basis and 030N primitive
element, lifting rational functions by units, exact Newton correction in a
square-zero ideal, and the 02HP retraction followed by tensor symmetry.
No new nodes or dependency modules were necessary; every dependency's recorded
notion is usable. No definitions, private copies, or proofs were introduced.
The sole theorem proof remains `sorry`. Imports are used, all variables and
universes are explicitly bound, and every Lean line is at most 100 characters.
The node's lean.statement was refreshed verbatim from the repaired signature.
The previous Worker report and earlier-reading section are preserved as history;
their assertion that Algebra.FiniteType expresses field generation is superseded
by this reading.

Validation: scompile.py compiled the single 66-line delivery module on the
server in 1.4 seconds, exit code 0, with no warnings or errors.
