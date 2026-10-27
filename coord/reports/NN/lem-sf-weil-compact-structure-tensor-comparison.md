## Worker report

The module `Sheaf.Paper.WeilCompactStructureTensorComparison` states
`AlgebraicGeometry.WeilComplex.native_compact_structure_tensor_comparison`.
Its sole theorem has proof `sorry`. Five supporting abbreviations/definitions
construct the two tensor/structure functors, their comparison from the given
projection/composition data, and the induced Hom equivalence. No objects are
chosen from mere existence, and no definition has postponed data.

The node is unchanged except for `lean`. There are no new nodes, dependency
repairs, or statement corrections, and no STATEMENT-DISPUTED issue.

Hypotheses and objects, clause by clause:

- The finite field is `(k₀ : Type u) [Field k₀] [Finite k₀]`. The prime and
  characteristic condition are `(l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`.
  As in the recorded native framework, the algebraic closure is its canonical
  `AlgebraicClosure k₀`, and the coefficient field is its `PadicAlgCl l`.
  Neither an independent coefficient category nor fixed pairs in a derived
  category replace the native category.
- `X Y : Scheme.{u}` and their `Over (Spec (CommRingCat.of k₀))` instances
  introduce the two k₀-schemes. Each structure map has `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact`, exactly separated finite type.
- `(f : X ⟶ Y) [f.IsOver ...] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]` is exactly the specified k₀-morphism. Its `IsOver` instance
  says `f ≫ (Y ↘ Spec k₀) = X ↘ Spec k₀`, the structure-map compatibility.
- `Spec (CommRingCat.of k₀)` is s₀, and `X ↘ ...`, `Y ↘ ...` are aX,aY.
  The imported `specOverSpec` structure competes with the identity structure
  over the base itself. The same fix already used upstream in
  `VerdierDualLocalization` is public priority 1100 for the existing
  `CategoryTheory.instOverClass`. This introduces no new notion, instance,
  or geometric hypothesis, and ensures the base is over itself by identity.
- `derivedLowerShriek k₀ l f` is F, and the same functor on the structure
  morphisms is AX/AY. `upperStar ... f` is the existing native termwise module
  pullback on the actual derived category, restricted to Weil complexes.
- M and L range over `WeilComplex k₀ l X` and `WeilComplex k₀ l Y` throughout.
  Membership of FM and f*L is expressed by the codomains of these restricted
  functors. Membership of both tensors is expressed by the codomain of the
  recorded `nativeConstructibleTensor`. Thus no extra membership hypothesis
  is imposed: the existing preservation results construct these objects for
  every M,L. The four objects are precisely F.obj M, upperStar.obj L,
  nativeCompactProjectionLeft.obj (M,L), and
  nativeStructureTensorInput.obj (M,L). All structure images likewise land in
  the full category `WeilComplex k₀ l (Spec k₀)`.

Conclusions, clause by clause:

- `nativeStructureTensorLeft` is `(M,L) ↦ AY(FM tensor L)`;
  `nativeStructureTensorInput` is `(M,L) ↦ M tensor f*L`;
  `nativeStructureTensorRight` is its composite with AX. These reuse the
  dependency's `nativeConstructibleTensor`, never a second tensor definition.
- The theorem supplies `pi : nativeCompactProjectionLeft ... ≅
  nativeCompactProjectionRight ...`, together with exactly the C,s,d,c data,
  `NativeOpenPresentationCompatibility`, and the underlying-arrow equation
  of `native_compact_projection_formula`. Consequently pi is pinned to the
  actual compactification proper counit mate, normalized open comparison and
  balanced pullback compositor, rather than an unspecified isomorphism.
- It supplies `gamma : AX ≅ F ⋙ AY`, the native functor composition
  isomorphism after the equality `comp_over f ...` identifies f≫aY with aX.
  This is the precise interface asserted by the recorded composition node.
- `nativeStructureTensorIso ... pi gamma` is the natural isomorphism
  `nativeStructureTensorLeft ≅ nativeStructureTensorRight`. Its actual data
  are `isoWhiskerRight pi AY` followed by `isoWhiskerLeft ... gamma.symm`.
  Thus its component is e, and naturality in both M,L is part of its NatIso
  type. The next conjunct writes the component formula explicitly as
  `AY.map (pi.hom.app (M,L)) ≫ gamma.inv.app (input.obj (M,L))`.
- The coefficient unit is exactly
  `WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec k₀))`, the rank-one
  coefficient module with canonical Weil action in degree zero, as specified
  in `def-sf-derived-weil-category-and-operations`.
- `nativeStructureTensorHomEquiv` uses Mathlib `Iso.homCongr` on e and the
  identity of that unit, hence is an actual `Equiv` of the displayed Hom sets.
  The next two conjuncts give its value `e.inv ≫ h` and its inverse's value
  `e.hom ≫ h'`. Its inverse laws belong to Equiv, so bijectivity is retained.
- The last two conjuncts quantify arbitrary u:M→M' and v:L→L' and give the
  contravariant square for the equivalence and its inverse. The product map
  `Prod.mkHom u v` passes through the actual source/target functors, so p is
  Fu tensor v and q is u tensor f*v, exactly the node's proof calculation.

Dependencies read and used:

- `WeilConjectures.WeilSheaf.LowerShriek`: `WeilComplex`,
  `WeilComplex.objectProperty`, `WeilComplex.derivedLowerShriek`,
  `ProEtaleWeilSheaf.rightDerivedLowerShriek`, and
  `WeilComplex.objectProperty_rightDerivedLowerShriek` (native framework and
  compact-support preservation). Their underlying category and pullback
  definitions were read in `WeilSheaf.Category`.
- `Sheaf.Paper.DerivedWeilOperations`:
  `ProEtaleWeilSheaf.nativeDerivedTensor`; ordinary tensor, total and
  K-flat model declarations were read, as were its imported coefficient unit
  `WeilSheaf.adicConstant` in `WeilSheaf.Constant` and `WeilSheaf.toComplex`
  in `WeilSheaf.Category`.
- `Sheaf.Paper.NativeCompactProjectionFormula`:
  `nativeConstructibleTensor`, `nativeCompactProjectionLeft`,
  `nativeCompactProjectionRight`, `nativeProjectionCompactification`,
  `nativeProjectionPullComp`, `native_compact_projection_formula`, and
  `ProEtaleWeilSheaf.NativeProjectionTensorComparison` /
  `nativeProjectionProperMate`. The complete source was also checked against
  the live server using `scompile.py --source`.
- `WeilConjectures.WeilSheaf.LowerShriekFunctoriality`:
  `WeilComplex.nonempty_derivedLowerShriek_comp_iso`; its full geometry and
  category binders and docstring were read.
- Proof imports: Mathlib `LocallyOfFiniteType`/`QuasiCompact`, `IsSeparated`,
  `QuasiSeparated`; `Sheaf.WeilSheaf.NativePullbackStarPreservation`:
  `native_pullback_star_preservation`; and
  `Sheaf.Paper.NativeDerivedWeilTensorConstructible`:
  `nativeDerivedTensor_mem_weilComplex`. The main docstring records all five
  DAG proof steps, including their dependency ids and naturality calculation.
- Mathlib `CategoryTheory.Iso.homCongr`, whose complete definition was read:
  toFun is inverse precomposition, invFun is forward precomposition.

The current blueprint sources were read in `literature/blueprint/latest/`:
`fix-cor-verdier-exchange.proof.md` Step 1 and
`fix-lem-tensor-adjunction.proof.md` Step 1. They give compact composition and
the inverse projection in the Hom chain, exactly the source places used here.

Edge cases checked: f=id, Y=Spec k₀, the empty X, M=0, L=0, non-lisse L,
and complexes with several nonzero degrees. None is excluded: there is no
nonempty-scheme, lissity, degree-zero, properness, or nonzero-object hypothesis.
In the zero/empty cases the same functor isomorphisms and Hom equivalences
still have their stated types. The Hom direction is correct: h has domain
AY(P), so e.inv:AX(K)→AY(P) precomposes it, and e.hom precomposes the inverse.
Universe u is explicit and shared with the native framework's schemes; the
larger site and sheaf universes are inherited without any new equality.

Searches for an existing statement:

- `msearch.py leanfinder`: “Projection formula and compact support composition
  give a natural structure pushforward tensor comparison for bounded
  constructible derived Weil sheaves”. Eight hits: ordinary
  SheafOfModules.pushforwardComp and its naturality/component lemmas,
  Scheme.Modules.pushforwardComp, and a LightCondensed internal-projectivity
  tensor criterion. None has native derived Weil shriek, the structure map,
  and the specified Hom equivalence.
- `msearch.py leansearch`: “Compactly supported cohomology of a tensor with
  Rf shriek is isomorphic to compactly supported cohomology of tensor with
  pullback in the native derived Weil category”. Eight hits: ordinary
  sheaf pullback/pushforward adjunction, pullback composition/isomorphisms,
  and restriction comparisons; none states this node.
- `msearch.py loogle`: `CategoryTheory.Functor.mapIso,
  CategoryTheory.Iso.homCongr`. One hit,
  `CategoryTheory.Functor.map_homCongr`; generic categorical calculus only.
- `msearch.py grep`, query `derivedLowerShriek|nativeCompactProjection|homCongr`
  in Mathlib CategoryTheory: 25 hits, all generic homCongr usages/definitions.
- `rg` of the item id in both upstream WeilConjectures and Sheaf: no match.
  `rg` for `nativeCompactProjection|compactStructureTensor|structure.*tensor`
  finds the projection dependency and unrelated structure/tensor material,
  but no combined structure comparison. A broader Hom/naturality search of
  native Weil modules finds only separate composition, lisse projection and
  derived Hom results. The exact new full declaration names were absent.

Validation: the delivered module passes both sandbox and actual-library-module
server compilations with scompile.py, no errors or warnings. Initial diagnostic
probes omitted the Lean `module` header and consequently exposed duplicates
hidden by the module system. Repeating the probe with the correct header
compiled cleanly; no dependency module or live file was changed for this.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
