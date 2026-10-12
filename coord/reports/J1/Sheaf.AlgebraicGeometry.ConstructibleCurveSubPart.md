## What changed

Replaced the sorry in `ConstructibleCurveSubPart.constructible_sub_part` by a real
reduction along the existing six-step route. The proof obtains a positive finite
annihilator, cancels the monomorphism to transfer it to the source, uses
`Scheme.constructible_torsion_modules_agree` twice, explicitly lifts the additive
inclusion to a linear natural transformation, reflects monicity through the
faithful forgetful functor, applies
`Scheme.isConstructibleEtaleModuleSheaf_of_mono_noetherian`, and transports back.
The existing signature and docstring are byte-for-byte unchanged.

Added the module `ConstructibleCurveAnnihilator` with the strict first-step lemma
`exists_annihilator_of_constructible`. All imports newly needed only by the proof
are plain imports. Updated the item's node to follow the actual reduction.

## Proved and sorry left

`AlgebraicGeometry.CurveCoefficientPair.constructible_sub_part` has a complete
proof body, conditional on the named unresolved dependencies. Its axiom closure
still contains `sorryAx`; it is not an axiom-free result yet.

The delivery adds exactly one named sorry:
`AlgebraicGeometry.CurveCoefficientPair.exists_annihilator_of_constructible`,
node `lem-weil-pbc-curve-constructible-annihilator`. The existing module comparison
and Noetherian subobject lemmas also remain open in the library.

## No longer needed

Removed proof-only imports:
- `Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `Sheaf.AlgebraicGeometry.CurveCoefficientPair`
- `Sheaf.AlgebraicGeometry.EtaleSheaves`
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `Sheaf.Paper.InverseImageStalkGerm`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The old proof dependency `lem-weil-pbc-curve-constructible-sub-quotient` is no
longer used by this node: it is the parent assembly, which already applies this
sub-part lemma, so retaining that dependency would give a circular plan.
No unit statement or realized step is bypassed; no whole library module is
claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The first worker's monomorphism core merely renamed the unresolved subobject
argument. `deliver3.py` correctly refused it as a restatement. Removed that module
and its node and replaced the reduction with the substantive module comparison,
linear lifting, and subobject-theorem application above. The original DAG named
the parent sub-quotient assembly as its sole dependency, although that assembly
already uses this theorem; the revised node records the noncircular ingredients.

## Second reading by J1

1. Compared the target module against the repository version. Existing signature
   and docstring are byte-for-byte identical; no definitions changed. Pass.
2. Both delivered modules compile without warnings through `lcompile.py`.
   Scratch `#print axioms` checks show only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The only delivered sorry is the named finite-bound
   lemma; no axiom, unsafe, opaque, implemented_by, extern, or hollow definition.
   Pass with the explicitly recorded open dependencies.
3. Checked the finite-bound statement and its complete docstring proof. Empty
   curve and zero sheaf permit n = 1; a finite constant stalk group is killed by
   the factorial of its cardinality; the finite product remains positive. This
   lemma supplies only the first step, rather than restating the target. Searches
   with LeanFinder, Loogle, Mathlib grep, and project/upstream rg found no existing
   matching theorem. LeanSearch was also attempted but returned Internal Server Error. Checked the cited Stacks definitions and Proposition 09BH
   online because literature is absent from this clone. Pass.
4. Read downward from the target, retaining the existing cyclic-module comparison
   and Noetherian subobject theorem. The lifted map's linearity uses that each
   ULift(ZMod n) scalar is a natural cast; its naturality is exactly the original
   additive naturality. The parent unit `sk-thm-p1` realized fields are unchanged.
   Removed imports and every unused old proof dependency are listed above. Pass.
5. The updated target node records the three actual proof dependencies. The new
   finite-bound node has its source, natural-language proof, three searches,
   creation data, blueprint link, unit/chapter, and exact Lean statement. Pass.

Second reading changed the rejected core split into a finite-annihilator split
and a real proof reduction; repaired metadata and pruning; preserved all existing
statements. No change record is needed.

## New nodes

`lem-weil-pbc-curve-constructible-annihilator` is the finite positive torsion-bound
step of the existing parent proof. Its source is the agent-written finite-bound
argument from the parent node, grounded in Stacks Definition 03RW and Lemma 095E;
the docstring gives the finite-cover and stalkwise argument in full. Sources:
[Definition 03RW](https://stacks.math.columbia.edu/tag/03RW),
[Lemma 095E](https://stacks.math.columbia.edu/tag/095E), and the application in
[Proposition 09BH](https://stacks.math.columbia.edu/tag/09BH).
