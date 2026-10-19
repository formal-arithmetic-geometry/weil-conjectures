## Worker report

The module `lean/Sheaf/SecSmoothPurity/LocalizedExtensionZeroLinearDerived.lean` states
`CategoryTheory.localizedExtensionZeroLinearDerived`. It gives an explicit compatible family
`rho : ∀ V, A →+* O.obj.obj V` for the phrase “sheaf of commutative A-algebras”; the theorem
argument `hnat` renders compatibility with every restriction. This is the sectionwise scalar
data used by the source argument and avoids an untyped implicit sheaf-algebra structure.

The conclusion has the following clauses, in order. The first existential is the `A`-linear
structure on module sheaves on `C`; the second is the corresponding structure on `C / U`.
The first universal clause renders sectionwise scalar multiplication on every module-sheaf
morphism, `(a • f).val.app V x = rho V a • f.val.app V x`. The second renders the localized
version, using `rho (Opposite.op V.unop.left)` for an object `V : (Over U)ᵒᵖ`. The next clause
is additivity of the localized extension functor
`SheafOfModules.localizedModuleExtension O U`, followed by its `Functor.Linear A` structure.
The remaining two existentials are the induced `A`-linear structures on the two unbounded
derived categories. Their final conjunction states additivity and `Functor.Linear` for the
termwise derived functor, `Nonempty CommShift ℤ`, and `IsTriangulated`.

The direct-sum and sheafification constructions are the recorded declarations used by
`localizedModuleExtension`; exactness is supplied by `SheafOfModules.localizedModuleExactIndependent`
and the derived functor and its triangulated structure by Mathlib
`CategoryTheory.Functor.mapDerivedCategory` and its instances. The proof docstring follows
five source steps: sectionwise central scalar actions; direct-sum scalar/additive formulas;
unique factorization through module sheafification; exact extension and termwise derived
functor; and Mathlib's exact-linear derived-functor instance.

Dependencies used by module imports are `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
(which supplies the localized extension and exactness interface) and
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (which supplies the termwise derived
functor, shift compatibility, triangulatedness, and induced linearity). The node's recorded
Mathlib dependencies are used for `Linear`, `Functor.Linear`, `DerivedCategory`, and the
triangulated structures. The size convention is represented by explicit universes and
`EssentiallySmall`; no extra geometric hypothesis is added.

Edge cases checked: zero ring and zero module sheaves; zero and unit scalars; an object with
no map to `U` (empty direct sum); an object with multiple maps to `U` (multiple direct-sum
summands); subterminal `U`; terminal `U`; and complexes unbounded in both directions. No
boundedness, resolution, flatness, subterminality, or nonzero coefficient assumption appears.

Searches made:

- `msearch.py ... leanfinder "module extension by zero linear on unbounded derived category of sheaves of modules over commutative algebra sheaf"`: hits generic derived-category linearity, with no extension-by-zero theorem.
- `msearch.py ... loogle "extensionByZeroPresheaf sheafification mapDerivedCategory Linear"`: no hits (the name is project-specific).
- `msearch.py ... grep "extensionByZero.*Linear|mapDerivedCategory.*Linear" Algebra/Homology/DerivedCategory`: one generic Mathlib hit at `ExactFunctor.lean:122`, not the sheaf-specific result.
- `rg` over the project and source for `extensionByZeroPresheaf`, `localizedModuleExtension`, and derived linearity: found the recorded localized extension and exactness modules, but no statement of this node.

No duplicate declaration was found. No new node, dependency repair, statement correction, or
`STATEMENT-DISPUTED` flag was needed. The source module was compiled with `scompile.py` and
finished without errors or warnings.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer fix (independent stage-2 review, 2026-10-18)

The delivered conclusion bound the two derived-category `A`-linear structures by
`∃ (_ : Linear A (DerivedCategory ...))`. A bound instance shadows Mathlib's
`DerivedCategory.instLinear`, so `Functor.Linear A (…).mapDerivedCategory` was stated for
arbitrary, unconstrained structures (for `A = ℤ[x]` the structure through `x ↦ 0` makes it
automatic), not for the structures induced by degreewise scalars and localization that the
node requires [lem-weil-linear-abelian-derived-category]. The fix removes those two
existentials; the derived clauses now use Mathlib's induced instance built from the two bound
module-sheaf structures (which the sectionwise clauses determine). It also removes the
redundant Prop instance hypotheses `HasSheafify`/`WEqualsLocallyBijective` for `J` and
`J.over U` (the dependency `LocalizedModuleExactIndependent` and the fixed file compile
without them) and the unused duplicate section variable `hnat`, and expands the docstring
proof to the node's five steps. Per-file compile through `nt_compile.py`: clean.
