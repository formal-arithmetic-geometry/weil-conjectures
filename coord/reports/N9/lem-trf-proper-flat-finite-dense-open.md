## Worker report

The module `lean/Sheaf/TraceFormula/ProperFlatFiniteDenseOpen.lean` states
`AlgebraicGeometry.proper_flat_finite_dense_open`. It introduces schemes `X` and `S`
of the explicit universe `u`, a morphism `f : X ⟶ S`, a target open `U : S.Opens`,
and concludes `IsFinite f`.

The hypotheses are rendered as follows: `[IsProper f]` is properness,
`[Flat f]` is flatness, `[LocallyOfFinitePresentation f]` is local finite
presentation, `(U : S.Opens)` is the open subscheme, `hU : Dense (U : Set S)` is
density of its underlying subset, and `[IsFinite (pullback.snd f U.ι)]` is
finiteness of the base changed morphism `X ×_S U ⟶ U`. The conclusion
`: IsFinite f` is finiteness of the original morphism. There are no additional
hypotheses or universe restrictions.

The statement dependencies used are Mathlib declarations: schemes and opens from
`Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.IsProper` from
`Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.Flat` from
`Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`AlgebraicGeometry.LocallyOfFinitePresentation` from
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`AlgebraicGeometry.IsFinite` from
`Mathlib.AlgebraicGeometry.Morphisms.Finite`, and
`CategoryTheory.Limits.pullback`/`pullback.snd` from
`Mathlib.AlgebraicGeometry.Pullbacks` and
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
The dependency node `def-sbc-locally-finite-presentation` receives a §1(B)
lean record pointing to the exact Mathlib class, because its prior node record
had no Lean declaration.

I checked the empty-open case (`U = ⊥`) and the identity-open case (`U = ⊤`):
the statement remains well typed and does not silently add nonemptiness or
surjectivity. The pullback map is the canonical `pullback.snd f U.ι`, rather than
an arbitrary map. I also checked that `Dense (U : Set S)` is the stated density
condition and that all schemes share the single explicit universe `u`.

Searches for an existing statement or duplicate were made with:

* `msearch.py ... leanfinder "A flat proper morphism locally of finite presentation that is finite over a dense open is finite"`: nearest results were `IsFinite`, `LocallyQuasiFinite`, and properness lemmas; no dense-open theorem.
* `msearch.py ... loogle "AlgebraicGeometry.IsProper, AlgebraicGeometry.Flat, AlgebraicGeometry.LocallyOfFinitePresentation"`: no hits.
* `msearch.py ... grep "IsFinite.*LocallyQuasiFinite|proper.*quasi-finite|finite.*dense" AlgebraicGeometry`: only separate proper/quasi-finite/finite lemmas.
* `rg` over `lean/Sheaf`, `WeilConjectures`, and Mathlib for `proper_flat_finite_dense_open`, `finite_dense_open`, and the pullback/density pattern: no existing declaration of this statement.

The module compiles cleanly with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N9 lem-trf-proper-flat-finite-dense-open lean/Sheaf/TraceFormula/ProperFlatFiniteDenseOpen.lean`.
The only postponed proof is the theorem body, as required for stage 2; its
docstring records the three proof steps from Tag 0B48 and names the proof nodes.

## Dependency modules

`def-sbc-locally-finite-presentation`: its original node had no `lean` record,
although the exact Mathlib declaration exists. The delivery copies the node and
adds the existing record for `AlgebraicGeometry.LocallyOfFinitePresentation` in
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`; no duplicate module is
needed.

## Second reading by N9

I reread the node, its source description, the module signature, and the
repaired dependency record. The morphism, proper/flat/local-presentation class
hypotheses, open `U`, density hypothesis, canonical pullback second projection,
finite base-change hypothesis, and finite conclusion all occur exactly once and
in the same roles. The explicit universe `u` is shared by `X` and `S`; no extra
assumption was introduced. The dependency repair names the exact Mathlib class
and leaves every other dependency field and the item's split report unchanged.
No mismatch was found.
