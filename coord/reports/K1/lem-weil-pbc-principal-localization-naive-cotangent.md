## Worker report

The delivery states `principal_localization_naive_cotangent` and defines the auxiliary
`NaiveCotangentComplex` structure. The theorem binds the rings, polynomial presentation,
surjective maps, localization, and kernels from the node. Its conjunction records kernel
generation, term isomorphisms, and equivalence of injectivity conclusions. The proof is
`sorry` as required for stage 2.

Dependencies used: `KaehlerDifferential` from `Mathlib.RingTheory.Kaehler.Basic`,
`MvPolynomial` from `Mathlib.Algebra.MvPolynomial.Basic`, and
`Localization.Away`/`IsLocalization.Away` from `Mathlib.RingTheory.Localization.Away.Basic`.

Edge cases checked: arbitrary (possibly empty) variable index via `Unit` extension,
non-domain rings, zero and unit localization elements, and arbitrary universes.
Searches found no existing project declaration or complete Mathlib theorem for the full
three-clause statement; Mathlib only supplies partial cotangent localization results.

## Earlier second reading (a previous round; superseded)

The theorem file and node were reread. Every ring, map, kernel, localization, and
surjectivity hypothesis appears as an explicit binder; the conclusion has the kernel
relation, two term equivalences, and injectivity equivalence. The auxiliary structure is
in its own module and cited by the item node.

## New nodes

`def-weil-pbc-naive-cotangent-complex` now records the existing Mathlib declaration
`Algebra.Extension.cotangentComplex` (Mathlib.RingTheory.Extension.Cotangent.Basic).
Its definition is NL(alpha) for a polynomial presentation: the conormal module I/I² in
degree 1, S tensor_P Ω[P/R] in degree 0, and the differential [f] ↦ 1 tensor df.
Source: Algebra, the paragraph defining NL(alpha), lines 35180–35203, used in 08JZ.
The DAG's smooth-ring-map definition concerns the canonical presentation and smoothness,
not the arbitrary-presentation complex; blueprint and definition-node searches found
no node carrying this exact notion. Loogle and source inspection found Mathlib's exact
construction, so no definition module is delivered. The first draft's bare-type structure
was not a naive cotangent complex and has been removed.


## Second reading by K1

This independent reading supersedes the mathematical claims in the initial Worker report
and the earlier second-reading paragraph. I opened the original item, its sandbox copy,
both draft modules, all three original dependency nodes and their Mathlib signatures,
and the new definition node. I read the Stacks source on the server: algebra.tex
35180–35203 (presentation and NL(alpha)) and 35605–35689 (08JZ and its proof).
08JZ assumes arbitrary commutative rings and a polynomial presentation; no finiteness,
Noetherian, nonzero-ring, or characteristic condition is assumed. The item's statement
is correct and unchanged; no statement_change or citer verdicts are needed.

Objects, hypotheses, and conclusions matched individually against the repaired Lean:

- A→B, arbitrary commutative rings: `{A : Type u} {B : Type v}`, `[CommRing A]`,
  `[CommRing B]`, `[Algebra A B]`. Exact.
- Variable set S, polynomial P=A[x_s], surjective A-algebra map alpha, kernel I:
  `{S : Type w}` and `(P : Generators A B S)`. I read Generators.lean:64–92,
  127–131, and 179–183: `P.Ring = MvPolynomial S A`, its algebraMap is `aeval P.val`,
  and the chosen section witnesses surjectivity. `P.ker` is precisely its kernel.
  Every surjective alpha admits such a bundle; the chosen section imposes no restriction
  and no conclusion depends on it. Exact bundled rendering of these objects.
- NL(alpha)=I/I²→Ω[P/A] tensor_P B: `P.toExtension.Cotangent`,
  `P.toExtension.CotangentSpace`, `P.toExtension.cotangentComplex`. I read
  Extension.Basic:330–437 and Extension.Cotangent.Basic:49–67: the conormal quotient
  has the B-action descended through alpha, the degree-zero module is
  `B ⊗[P.Ring] Ω[P.Ring⁄A]`, and `[f]` maps to `1 ⊗ df`. Tensor symmetry reverses
  the source's tensor order, without changing its module or map. Exact.
- g∈B, f∈P with alpha(f)=g: `(g : B) (f : P.Ring)` and
  `(hf : algebraMap P.Ring B f = g)`. Exact.
- Bg is localization at powers of g: `{Bg : Type z}`, its CommRing and B-algebra
  instances, `[IsLocalization.Away g Bg]`. The A-algebra and
  `[IsScalarTower A B Bg]` make explicit the induced composite A→B→Bg; they do not
  introduce an independent A-action or an extra ring hypothesis. The original dependency
  records Localization.Away, and ring-localization Away.Basic supplies this exact
  characterization. Exact, without fixing a localization model or universe.
- beta is alpha followed by B→Bg on old variables and x↦1/g:
  `(Q : Generators B Bg Unit) (hQ : Q = localizationAway Bg g)` and `Q.comp P`.
  I read localizationAway and comp (Generators.lean:208–244): the sole new variable
  is sent to `IsLocalization.Away.invSelf g` and each old variable to the composite.
  `MvPolynomial (Unit ⊕ S) A` is P[x] under the canonical polynomial flattening.
  This naming equality fixes Q to the specified canonical presentation; it adds no
  mathematical assumption and allows every choice of Bg above. Exact.
- J=ker beta: `(Q.comp P).ker`. Exact, determined rather than arbitrary.
- beta surjective: first conjunct `Function.Surjective (aeval (Q.comp P).val)`.
  It is a conclusion, not the old hbeta assumption. Exact.
- J generated by I and fx−1: second conjunct, `Ideal.map ... P.ker ⊔ Ideal.span {...}`.
  `Q.toComp P` is the old-variable inclusion, definitionally `rename Sum.inr`, as read
  in Generators.lean:523–531. Exact, includes the omitted ideal I.
- Clause (1), including the induced inclusion and the specified rank-one generator:
  existential `r` names fx−1 as a member of J; `e1` is a Bg-linear equivalence
  `J/J² ≃ (Bg ⊗[B] I/I²) × Bg`. Its inverse formula is the scalar extension of
  `Extension.Cotangent.map (Q.toComp P).toExtensionHom` on the first summand plus
  `b • Extension.Cotangent.mk r` on the second. Exact; a finite two-summand product
  is the direct sum. Freeness on the specified class follows from this equivalence.
- Clause (2), including dx and the old differential summand: `e2` is a Bg-linear
  equivalence between the new differential module and the old base change times Bg.
  Its inverse formula uses the induced `CotangentSpace.map` and `1 ⊗ D x`.
  I read CotangentSpace.map and map_tmul, not merely the declaration names.
  The old module is `Bg ⊗[B] (B ⊗[P.Ring] Ω[P.Ring⁄A])`, canonically
  `Bg ⊗[P.Ring] Ω[P.Ring⁄A]` by tensor associativity. Exact.
- Clause (3), chosen decompositions forming an isomorphism of complexes:
  `e1` and `e0` are invertible Bg-linear maps in degrees 1 and 0; `e0` fixes the
  canonical old summand, and the universal `(∀ a b, ...)` equation says exactly that
  delta_beta is conjugate to `(delta_alpha.baseChange Bg, b ↦ g*b)`.
  This is precisely an isomorphism of these two-term complexes, with no unstated
  differential compatibility. Exact. Its new degree-zero generator is necessarily
  g⁻²df+dx, since g is a unit, as in the source proof.
- Injectivity of the localized old differential iff injectivity of beta's differential:
  the explicit `Function.Injective ... ↔ Function.Injective ...` conjunct compares
  `P.toExtension.cotangentComplex.baseChange Bg` with the actual beta differential.
  Exact; it does not compare the unlocalized alpha differential.
- Isomorphic cokernels: final `Nonempty (... ≃ₗ[Bg] ...)` compares the degree-zero
  quotient modules by the ranges of these same differentials. Exact, linear rather
  than an equivalence of sets.

Edge cases: S may be empty or arbitrarily large (`Type w` independently of A and B);
there is no finite-variable or n>0 restriction. A, B and Bg may be zero rings. g=0,
g=1 and nilpotent g are all covered; in the collapsed localization all displayed
modules and the rank-one free Bg summand become zero, consistently. Every
characteristic is permitted. Bg has an independent universe z and tensor/module
universes are inferred as maxima; there is no independent test-object quantifier that
could become vacuous. Empty schemes and index diagrams do not occur in this ring lemma.

Independent searches (with source inspection of every candidate):
- LeanFinder via msearch, “cotangent complex polynomial presentation localization away
  splitting”: cotangentCompLocalizationAwayEquiv and its inverse formulas. They give
  clause (1), not all clauses of this node; their signatures do not include the
  differential-module or complex splitting, nor both final conclusions.
- Loogle via msearch, `Algebra.Extension.cotangentComplex`: exact existing presentation
  differential, plus its related homology statements. Used, not duplicated.
- LeanSearch via msearch, “naive cotangent complex of a surjective polynomial
  presentation”: service unavailable (Internal Server Error); no negative verdict
  inferred from that service failure. Loogle, LeanFinder, and grep were available.
- Grep via msearch, `cotangentCompLocalizationAwayEquiv|cotangentComplex|
  principal_localization_naive_cotangent`; direct rg with “Cotangent”, “CotangentSpace”,
  “naive cotangent”, “08JZ”, and “compLocalization” in Mathlib, WeilConjectures,
  lean/Sheaf, dag/nodes and dag/lean_names_upstream.json; blueprint_refs.py search
  cotangent. No exact whole-node statement exists; Mathlib supplies the partial
  kernel/conormal lemmas and all the notions. PresentationsHomotopyEquivalent and
  CotangentComplexSymmetricAlgebra concern different statements and use the same
  Mathlib differential. The full new theorem name does not already exist.

Mismatches repaired: the original P was an arbitrary algebra unrelated to S; alpha,
beta and the localization actions were unrelated; beta surjectivity was assumed;
J's formula omitted I; arbitrary bare-type NLα/NLβ were unrelated to presentations,
not modules, and their unlocalized term equivalences were false; the module
splittings, generators, differential compatibility and cokernel conclusion were missing.
I replaced that malformed signature by the exact bundled polynomial presentation and
all the maps/conclusions listed above. The new definition node was also wrong: a pair
of types with a function is not NL(alpha), and Mathlib already defines the actual notion.
I replaced its definition statement and record by the exact existing Mathlib construction,
added its polynomial/differential dependencies, retained its required provenance fields,
and removed its redundant module. Its source paragraph explicitly defines this notion.
No item natural-language statement, proof step or original dependency record changed.

Conventions and validation: one genuine theorem with its proof `sorry`; no new hollow
definition and nothing proved. Header, namespace, source-tagged module and declaration
docstrings, all eight natural-language proof steps, and ≤100-character lines checked.
The item lean.statement is extracted verbatim from the keyword through the signature.
Server scompile completed cleanly (no errors or warnings), using its pinned Mathlib.
