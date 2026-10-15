## What changed

`WeilConjectures.WeilSheaf.Finiteness` now has complete Lean proofs at both original holes,
with every existing signature unchanged. For compact support, negative degrees follow directly
from exact extension by zero and left t-exactness of the derived proper pushforward. For the
upper bound, every finite coefficient group is zero by the existing etale compact-support
cohomological-dimension theorem; an injective comparison then transfers vanishing to adic
cohomology. The proper ordinary-cohomology statement follows through the existing
Frobenius-equivariant compact/ordinary comparison.

The finite coefficient groups are constructed explicitly in
`Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison`: apply etale derived lower shriek
to the finite constant unit sheaf on the geometric fibre, take the cohomology sheaf and its
sections, then restrict scalars along `PadicInt.toZModPow`. The coefficient ring is the universe
lift of `ZMod (l ^ (n + 1))`. No definition contains a hole or chooses data from a holed
existence assertion.

The sole new unresolved theorem is the dimension-independent comparison embedding into
`PadicAlgCl l ⊗[PadicInt l] (∀ n, finiteLevelCompactSupportSections l X n r)`. Its docstring and
node give the finite-level/derived-limit/flat-extension proof and sources. It is only a
coefficient comparison: it contains no dimension parameter and no vanishing conclusion.
The actual cohomological bound, including all geometric-fibre dimension checks, is Lean code
in the assigned module. The unit's finite-to-integral-to-rational route is retained.

The existing `WeilSheaf.IsUnitCompatible.lowerStar` proof was also replaced by the already
proved `lowerStar_unit_str`. This avoids the original long categorical rewrite term's kernel
checking timeout. Its signature and all other existing declarations are unchanged.

Removing the unused PoincareDuality public import forces one adaptation in the unclaimed
`WeilConjectures.ZetaFunction.TraceFormula`; see the final section. Change record:
`coord/changes/F1-finiteness-prune-duality.md`.

Validation: the three delivered Lean files compile together in import order with no errors or
warnings (approximately 3, 9 and 4 seconds). The eight other direct importers and the three indirect duality users
(BettiSymmetry, DualityReciprocity and SmoothProper) were separately compiled from scratch copies against the changed sandbox overlay; all passed.
Only single-file compilation through lcompile.py was used. Scratch consumers were removed
from the delivery and compiled overlay after these checks.

## Proved and sorry left

Original holes closed (2):

- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_adicConstant`:
  complete combining proof; negative degrees proved directly; positive degrees reduced to
  the existing finite-coefficient bound and the new comparison below.
- `AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant_of_isProper`:
  complete transport proof from compact support through the already available linear
  equivalence. No separate new obligation for the proper case.

New hole (1):

- `AlgebraicGeometry.WeilSheaf.exists_injective_compactSupportFiniteCoefficientComparison`,
  node `lem-pod-compact-support-finite-coefficient-comparison`, in the new module
  `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison`.

No hole remains in Finiteness. The adapted TraceFormula retains its pre-existing hole
`AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_eq`
(node `thm-trf-grothendieck-lefschetz-qbar`) unchanged;
no hole is added there. This is a decomposition of the
compact-support bound, with two upper holes closed and one genuinely different lower hole
added (file-level net one hole removed), not an axiom-free proof of the entire finiteness
theorem. The project closure ledger also accounts for imported dependencies.
The existing finite-coefficient cohomological-dimension declaration is itself still `sorry`
in its own module; it is used as intended by stage 3 and is not changed here.

What the new hole still needs: construct the constant integral pro-etale lattice and its
coherent finite reductions; compare the actual `WeilSheaf` adic compact-support calculation
with the derived inverse limit of these reductions; identify its rationalization/field
extension with the tensor product in the statement; use finite torsion finiteness and the
Milnor sequence to embed integral cohomology into the product. The project has normalized
adic towers, their range and realization APIs, and abstract Mittag-Leffler/flatness tools,
but the actual Qbar-adic sheaf model is not yet connected to the integral model by a usable
comparison. This is also explicitly listed as missing infrastructure in
`SixFunctors/ProEtale/Adic/LowerStar.lean`. Merely importing the tower API does not supply this
identification. In particular,
`ProEtale.AdicSystem.compactSupportTower_realization` concerns an explicitly supplied normalized
finite-coefficient system. The coefficient-extension instances in
`SixFunctors/ProEtale/ModuleObject/Colimit/Compatibility.lean` concern the condensed-ring module
model; connecting that model to the actual `AdicSheaf` over `WeilCoefficients` and its derived
cohomology is still necessary. Their remaining proofs being `sorry` would not prevent using
them in stage 3; it is the missing comparison data, not those holes, that prevents a direct
application here.

The final algebraic step was verified separately in Lean: `Module.Flat.trans (PadicInt l)
(Padic l) (PadicAlgCl l)` supplies flatness, and
`Module.Flat.lTensor_preserves_injective_linearMap` proves injectivity of base change. These
scratch experiments are not unused additions to the library. A second algebra experiment
constructs the product reduction map `Z_l -> ∏ n, Z/l^(n+1)`, proves injectivity via
`PadicInt.ext_of_toZModPow`, and proves the injection remains injective after base change.
Thus the point-case algebra and its Z_l scalar actions were checked by compiled Lean.
Finite towers satisfy Mathlib
`Functor.isMittagLeffler_of_exists_finite_range`; the specialization using the identity
map and finiteness of its range was also compiled in scratch.

## No longer needed

Removed public import `WeilConjectures.WeilSheaf.PoincareDuality`. None of its declarations,
including smooth proper vanishing or the perfect pairing, is used by the new Finiteness proof.
That module remains needed elsewhere in the project; this delivery makes no global
unreachability claim and does not edit it (it is held by F3).

Removed redundant direct public imports:
`WeilConjectures.WeilSheaf.Cohomology`, `WeilConjectures.WeilSheaf.Constant`,
`WeilConjectures.WeilSheaf.LowerStar`, and `WeilConjectures.WeilSheaf.StalkPairing`.
Their declarations are still needed and are publicly available through retained imports.
`ConstantTwistCohomology` is retained because the existing proper comparison uses its
`globalSectionsEquivOfIso` API.

The old constant-coefficient range argument no longer needs these nodes:

- `def-weil-finite-tor-amplitude`;
- `lem-coef-integral-compact-support`;
- `def-weil-point-fg-complete-complexes`;
- `lem-pod-point-sections-derived-reduction`;
- `lem-pod-dvr-complex-amplitude-mod-uniformizer`.

The stronger integral Tor-amplitude and derived Nakayama route is replaced by finite-group
Mittag-Leffler and an inclusion into the product. These are pruned from this argument, not
withdrawn globally. None of their modules is imported for the delivered proof.

Also removed as direct proof dependencies of the parent node are
`lem-weil-constant-coefficient-objects-constructible`,
`def-weil-integral-rational-qbar-compact-support`, and
`def-weil-l-adic-coefficient-extension`. Those three still occur below the new comparison node
and are not globally pruned. `lem-dg-compact-support-amplitude` and the new comparison node
are the two new direct proof dependencies. All remaining parent steps and statement fields
are retained.

## Where the brief, the DAG or earlier work was wrong

The parent node has no Lean attachment despite the module's blueprint annotations, and
several of its planned integral-stage dependencies have no Lean declaration attached.
The usable finite-coefficient dimension bound is already in the source library as
`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerShriek_singleFunctor_of_two_mul_lt`,
although `lem-dg-compact-support-amplitude` also has no Lean attachment in its node.
No duplicate finite-coefficient statement was introduced.

The baseline assigned module itself exceeded the 60-second limit while checking the
pre-existing `IsUnitCompatible.lowerStar` proof. Reusing the existing specialized lemma,
without changing definitions or increasing any limit, removes that problem.

The new comparison was checked against the primary references (Bhatt-Scholze,
`https://people.mpim-bonn.mpg.de/scholze/proetale.pdf`, §§6.5, 6.7-6.8, and Milne,
`https://www.jmilne.org/math/CourseNotes/LEC.pdf`, §§18-19). Its elementary edge cases agree:
empty schemes give zero, negative degrees give zero, level zero means the nonzero ring
`ZMod l`, singular/nonproper schemes are allowed via compactification, and no claim of
vanishing is made at the endpoint `r = 2e`. Products and tensor products use Z_l scalars,
not an unrelated integral scalar action. All data is constructed explicitly.

The completeness check uses the pro-etale, rather than etale, extension by zero:
Bhatt-Scholze Lemma 6.1.13 says it commutes with homotopy limits, and Lemma 6.5.8
says it preserves constructibility. These precise inputs are included in the comparison
docstring and node. Thus the integral inverse-limit step is not assumed from mere
exactness of extension by zero.

No target statement or existing intermediate signature is disputed or changed.

## New nodes

`lem-pod-compact-support-finite-coefficient-comparison`, in
`dag/nodes/sec-poincare-duality/lem-pod-compact-support-finite-coefficient-comparison.json`:
a dimension-independent coefficient-comparison embedding for the actual constant Weil sheaf.
The proof uses its specified constant integral lattice, finite torsion finiteness,
Mittag-Leffler/Milnor, and flat extension from Z_l to Qbar_l. The natural-language proof,
three available Mathlib search kinds plus the recorded unavailable LeanSearch attempt, Lean
attachment, source and origin are included. What remains to formalize is listed above.
The parent `prop-cohomological-finiteness` copy changes only proof, proof_deps and proof_origin.
The unit record `sk-lem-finite` is untouched; its realized arrays are empty and the unit route
through coefficient stages is preserved.

Change record: `coord/changes/F1-finiteness-prune-duality.md`.

## Forced adaptations

Adapted module: `WeilConjectures.ZetaFunction.TraceFormula`, unclaimed when checked.
The original source compiled against the pruned Finiteness overlay fails at its line 251:

```text
error(lean.unknownIdentifier): Unknown constant
'AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant'
```

That smooth-proper theorem was provided only by the removed public PoincareDuality import.
The adaptation adds the private import (new line 14)
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` and replaces the failing invocation
at new lines 252-260 with the Finiteness theorem `subsingleton_cohomology_adicConstant_of_isProper`. Its dimension
hypothesis is supplied by `topologicalKrullDim_le_of_smoothOfRelativeDimension`, applied to the
base change of the given smooth relative dimension. These are exactly the proof lines needed
to replace the unavailable declaration; every existing signature and visibility is unchanged.
The adapted module compiles against the changed dependencies. The retained mention of the
original smooth-proper theorem in its docstring is historical explanatory text, not an import
or a dependency of the proof.

## Second reading by F1

1. **Statements and signatures.** I compared each delivered module with the repository
   version and checked the declarations used by downstream modules. Existing theorem
   signatures and definitions are unchanged; the parent DAG node changes only its recorded
   proof route and dependencies. The new finite-level definition and comparison theorem use
   the stated geometric fibre, coefficients, degree, and scalar actions. Verdict: pass.
2. **Proof and axioms.** All three delivered modules compile together with `lcompile.py
   --all`. Finiteness has no remaining holes; the only new hole is the named comparison
   theorem, with its source, proof sketch, and DAG node. The unrelated pre-existing
   TraceFormula hole is unchanged. No forbidden declarations or hollow definitions occur.
   Verdict: pass.
3. **New statement review.** I searched the library and Mathlib by name and concept and
   checked edge cases (empty schemes, negative degrees, level zero, nonproper schemes, and
   the endpoint). No duplicate declaration was found. The comparison is a genuine lower-level
   coefficient-comparison obligation and makes no dimension or vanishing claim. Verdict: pass.
4. **Pruning and route.** I rechecked every changed import and the parent node's proof
   dependencies against the compiled proof. The removed duality and redundant public imports
   are unused; the finite-coefficient and flat-comparison imports are used. The shorter
   negative-degree and finite-level routes retain the unit's finite-to-integral-to-rational
   route through the parent steps and comparison node. Verdict: pass.
5. **DAG agreement.** I compared each changed proof step and `proof_deps` entry with the Lean
   code, and checked the new node's statement, source, proof origin, Lean attachment, chapter,
   and unit. The change record names the forced TraceFormula adaptation and its unchanged
   signature. Verdict: pass.

I changed only this report by adding the second-reading record; no proof or statement changes
were needed after review.
