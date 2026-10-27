## Worker report

Attached the exact existing declaration
`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_comp_iso`
in `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` (lines 188–201).
The local source and the current server source, read with
`scompile.py --source WeilConjectures.WeilSheaf.LowerShriekFunctoriality`, agree.
The declaration already has `sorry`, appropriate to stage 2. No Lean module,
new definition, dependency repair, or statement correction is required.
Only the item's `lean` record changes.

The previous worker's stale-assignment conclusion concerned the Q18 stage-1
split (ledger entry at line 24790). This is a stage-2 task: the live node is
split and reviewed but had no `lean` field. Its exact existing Lean statement
can therefore be attached without resplitting it. No repair note exists at
`coord/repair-notes/lem-sf-native-weil-shriek-composition.json`.
The retired CompactObject example was also read; its node now points to the
upstream declaration and its Sheaf module contains no declarations.

Hypothesis-by-hypothesis correspondence (node `V,W,T,a,b` are Lean `X,Y,Z,f,g`):

| Node text | Existing Lean binders or expression |
| --- | --- |
| Finite field `k₀` | `{k₀ : Type u} [Field k₀] [Finite k₀]` (line 54) |
| Prime `ℓ`, different from the characteristic | `{l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]` (line 54) |
| `Ω = Q̄_ℓ` with the native coefficient convention | `WeilComplex k₀ l X` and its dependency's `ProEtale.AdicSheaf l` use `PadicAlgCl l` and `adicConstantSheaf l`; no arbitrary coefficient ring is substituted |
| Three `k₀`-schemes | `{X Y Z : Scheme.{u}}` and the three `[X.Over (Spec (CommRingCat.of k₀))]`, `[Y.Over ...]`, `[Z.Over ...]` section binders |
| Composable maps `V → W → T` | `(f : X ⟶ Y) (g : Y ⟶ Z)` |
| Maps over `k₀` | `[f.IsOver (Spec (CommRingCat.of k₀))]`, `[g.IsOver (Spec (CommRingCat.of k₀))]` |
| `a` separated, quasi-compact, locally finite type | `[IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]` |
| `b` separated, quasi-compact, locally finite type | `[IsSeparated g] [QuasiCompact g] [LocallyOfFiniteType g]` |
| `W` locally finite type over `k₀` | `[LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]` |
| `W` quasi-compact | `[QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]` |
| `W` quasi-separated | `[QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]` |
| `T` locally finite type over `k₀` | `[LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]` |
| `T` quasi-compact | `[QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]` |
| `T` quasi-separated | `[QuasiSeparated (Z ↘ Spec (CommRingCat.of k₀))]` |

No absolute separatedness of `X`, `Y`, or `Z` over the field is assumed.
For schemes over a field the quasi-compactness and quasi-separatedness of
the structure morphism agree with those intrinsic scheme properties; the
base is affine and separated. There is no extra hypothesis on `V`.
Universe `u` is declared explicitly in the upstream module. All identifiers
in the recorded signature come from explicit section or theorem binders.

Clause-by-clause correspondence:

- Existence of an isomorphism is `Nonempty (...)`.
- It is an isomorphism of functors, expressed by `≅` between functors, not
  separate unrelated isomorphisms on individual objects or cohomology groups.
- `R(ba)₀!` is `derivedLowerShriek k₀ l (f ≫ g)`.
- `Rb₀! ∘ Ra₀!` is `derivedLowerShriek k₀ l f ⋙ derivedLowerShriek k₀ l g`;
  Lean's `⋙` applies the first functor and then the second.
- Both functors have domain `WeilComplex k₀ l X` and codomain
  `WeilComplex k₀ l Z`, from the definition's full signature.
- These are the native derived Weil categories, full subcategories of
  `DerivedCategory (ProEtaleWeilSheaf k₀ l X)`, not fixed pairs in the derived
  category of ordinary coefficient sheaves. Their morphisms and therefore
  the natural isomorphism components retain the Weil structure. Equivariance
  is built into the conclusion, with no separate action or arbitrary map.

Dependency declarations read and used:

- `def-sf-native-weil-derived-framework`: entry module
  `WeilConjectures.WeilSheaf.LowerShriek`, declaration
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek` (lines 150–162), its
  ambient construction `ProEtaleWeilSheaf.rightDerivedLowerShriek` (line 88),
  and `hasCompactification_of_over`. It is extension by zero followed by the
  right derived direct image for the chosen Nagata compactification,
  restricted using the bounded-constructible object property.
  Read the underlying category and operation interfaces in
  `WeilConjectures.WeilSheaf.Category`: `WeilSheaf.frobeniusPullback`,
  `ProEtaleWeilSheaf`, `WeilSheaf.objectProperty`,
  `WeilComplex.objectProperty`, `WeilComplex`,
  `ProEtaleWeilSheaf.upperStar` and `WeilComplex.upperStar`;
  in `WeilConjectures.WeilSheaf.LowerStar`:
  `ProEtaleWeilSheaf.lowerStar`, `WeilComplex.derivedLowerStar`;
  and in `WeilConjectures.WeilSheaf.OpenImmersion`:
  `ProEtaleWeilSheaf.extensionByZero`.
  Read also `ProEtale.AdicSheaf` in
  `WeilConjectures.SixFunctors.ProEtale.Adic.Module`,
  `PadicAlgCl.locallyFiniteFunctions` and `ProEtale.adicConstantSheaf` in
  `...Adic.ConstantSheaf`, and `ProEtale.IsAdicLisseSheaf`,
  `IsAdicStratifiedLisseSheaf`, `IsAdicConstructibleSheaf` in
  `...Adic.Constructible`. These confirm whole-space continuous locally
  finite functions, finite rank allowed to vary by cover member, and bounded
  constructible cohomology as specified by the recorded dependency.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`, with `IsSeparated` from
  `Mathlib.AlgebraicGeometry.Morphisms.Separated` and `UniversallyClosed`
  from `...Morphisms.UniversallyClosed`. Only the node's separatedness
  notion enters the statement: the diagonal is a closed immersion.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` (line 43), and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `AlgebraicGeometry.QuasiCompact` (line 43). Finite type is their
  conjunction, so the node and Lean assumptions coincide.
- `def-weil-quasi-separated-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
  `AlgebraicGeometry.QuasiSeparated` (line 50), requiring a quasi-compact
  diagonal.

The exact existing theorem's docstring and full signature, including section
binders, were read. The source is the node's own cited upstream declaration;
Stacks `more-etale.tex`, Tag 0F7J, `lemma-shriek-composition` (lines 3158ff.)
was read for the compactification calculation. That ordinary etale result is
not substituted for the native Weil statement. The node's five proof steps
retain the native comparison and interchange inputs. No proof is supplied
in this stage-2 attachment and no upstream file is changed.

Edge cases checked at the statement level:

- Identity maps satisfy the morphism assumptions; no distinctness or
  nonidentity restriction occurs. The conclusion still compares the actual
  chosen compactification functors.
- Empty schemes are permitted by the scheme and morphism binders, with no
  nonempty-source assumption; the zero Weil complex is also included.
- `W,T` may be quasi-separated and nonseparated over the field. Only `f,g`
  are required to be separated. No properness of `f` or `g` is introduced.
- All prime coefficients different from the characteristic are retained.
- `V` need not be separately assumed qcqs or finite type over the field:
  its requisite properties follow from `f` and `W`, and the existing theorem
  does not introduce them as additional binders.
- The conclusion asserts existence only. Independence of the choice of
  compositor, a specified canonical map, or coherence is not added.

Searches executed for this delivery:

1. `msearch.py NR lem-sf-native-weil-shriek-composition leanfinder
   "Composition of compactly supported derived direct images on native
   Frobenius equivariant Weil complexes"`: OK, 8 hits. Ordinary scheme/module
   and sheaf/presheaf pushforward composition and isocrystal equivariance;
   none states native Weil compact-support composition.
2. `msearch.py ... loogle '"derivedLowerShriek"'`: OK, 0 hits.
3. `msearch.py ... grep
   'derivedLowerShriek|shriek.*comp|compact.support.*compos'`: OK, 0 hits.
4. `rg -n 'nonempty_derivedLowerShriek_comp_iso|derivedLowerShriek.*[Cc]omp|shriek.*[Cc]omp'
   lean/WeilConjectures lean/Sheaf`: found the exact upstream theorem at
   `WeilSheaf/LowerShriekFunctoriality.lean:188` and wrappers in
   `LowerShriekPackage.lean` / `LowerShriekOperations.lean`; many unrelated
   finite-coefficient and abstract shriek results in Sheaf. The narrower
   `rg -n 'nonempty_derivedLowerShriek_comp_iso'
   lean/WeilConjectures lean/Sheaf dag/lean_names_upstream.json` confirms the
   declaration in the upstream-name index, and finds no duplicate Sheaf
   declaration. Use the primary theorem named by the node's source.
5. `rg -n 'lem-sf-native-weil-shriek-composition' lean/WeilConjectures`:
   no occurrence of the new DAG id. Searching by the actual statement and
   source declaration, rather than just the new id, found the exact match.

No node fault or STATEMENT-DISPUTED issue remains. There are no new nodes,
no dependency modules, and no delivered Lean files. Validation uses the
prescribed delivery wrapper, which calls scompile.py on a module-mode
`#check @AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_comp_iso`
probe and runs server preflight. The maintainer supplies independent review.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
