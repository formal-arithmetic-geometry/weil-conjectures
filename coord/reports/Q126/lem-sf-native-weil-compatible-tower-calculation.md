## Worker report

The module `Sheaf.WeilSheaf.NativeCompatibleTowerCalculation` states
`AlgebraicGeometry.WeilComplex.nativeWeilCompatibleTowerCalculation`, with one whole-proof
`sorry` and no new definitions. The node changes only in `lean`; its natural-language
statement and dependency lists are unchanged.

Source read: `literature/stacks-project/more-etale.tex`, Tag 0F7J,
`lemma-shriek-composition`, lines 3159–3209, particularly its first four displayed
identifications. Its geometric compactification calculation is adapted to the native
coefficient realization explicitly specified by the node. The torsion étale theorem is
not used as a theorem about these coefficients. The native framework's actual declarations
and both native comparison statements were read in full.

Hypothesis and clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Finite field k₀ | `(k₀ : Type u) [Field k₀] [Finite k₀]` |
| Prime ℓ different from the characteristic | `(l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]` |
| Ω = algebraic closure of Q_ℓ, with framework coefficients | The coefficient parameter `l` in `ProEtaleWeilSheaf k₀ l X` uses exactly the framework's `PadicAlgCl l` and locally finite function sheaf; no independent coefficient ring or arbitrary action is introduced. |
| Six k₀-schemes V,U,Vbar,W,Wbar,T | Six `Scheme.{u}` binders and their six `.Over (Spec (CommRingCat.of k₀))` instances |
| Each is finite type over k₀ | A `LocallyOfFiniteType` and a `QuasiCompact` binder for each of the six structure maps; this is exactly the recorded finite-type dependency's convention. |
| The six maps s,t,i,p,pW,q are k₀-maps | Six typed morphism binders with six `.IsOver` instances |
| s,t,i quasi-compact open immersions | `[IsOpenImmersion s] [QuasiCompact s]` and the corresponding pairs for `t,i` |
| p,pW,q proper | `[IsProper p] [IsProper pW] [IsProper q]` |
| pt = ipW is Cartesian | `(hcart : IsPullback t pW p i)` includes both commutativity and the universal property, in the correct square orientation. No independent commutativity or stronger square assumption is added. |
| a = pW s, b = qi, z = ts | These are expanded as `s ≫ pW`, `i ≫ q`, and `s ≫ t`; only `z` occurs in the functor formula, so no unused maps or equality hypotheses are introduced. The equalities pz = ia and qpz = ba follow from `hcart.w` and associativity. |
| F_(j,r) = Rr_* J_j for the given factorizations | Expanded as `(extensionByZero k₀ l j).mapDerivedCategory ⋙ (lowerStar k₀ l r).rightDerivedFunctor`. This is the body of the framework's `ProEtaleWeilSheaf.rightDerivedLowerShriek`, with the explicitly supplied factorization, not a newly chosen compactification. The compactification dependency's `Compactification` and `Refinement` were read; no second compactification structure is defined. |
| J_s carries WC^der(V) into WC^der(U) | First conjunct: every native derived `K` satisfying `objectProperty k₀ l V` has extension satisfying `objectProperty k₀ l U`. This states preservation, rather than assuming it. |
| First intermediate derived identification | Second conjunct, `Nonempty` of the natural isomorphism from `ι_V ⋙ J_(s≫t) ⋙ R(p≫q)_*` to `ι_V ⋙ J_s ⋙ J_t ⋙ Rp_* ⋙ Rq_*`. Left-to-right Lean functor composition is right-to-left application in the displayed mathematical formula. |
| Middle proper/open identification on J_s K only | Third conjunct, between `ι_V ⋙ J_s ⋙ J_t ⋙ Rp_* ⋙ Rq_*` and `ι_V ⋙ J_s ⋙ RpW_* ⋙ J_i ⋙ Rq_*`. Both have precisely the bounded constructible source `WC^der(V)` via `objectProperty.ι`; the first conjunct permits restricting the recorded proper/open comparison along J_s. No comparison on arbitrary unbounded U-inputs is asserted. |
| Natural endpoint isomorphism F_(z,qp) ≅ F_(i,q) F_(s,pW) | Fourth conjunct, `Nonempty` of the natural isomorphism between the second conjunct's initial functor and the third conjunct's final functor. The docstring specifies composition of the two intermediate comparisons. |
| All isomorphisms and inverses are native equivariant | The functor codomain is the ordinary `_root_.DerivedCategory (ProEtaleWeilSheaf k₀ l T)`. A functor isomorphism `≅` has native natural transformations as both hom and inv, with inverse identities; it is not a mere cohomology identification or a forgotten non-equivariant isomorphism. |
| No absolute separatedness and no assertion on arbitrary unbounded inputs | There is no `IsSeparated` binder for any structure map. The functors accept only the full bounded constructible source through `ι_V`; no preservation assertion for intermediate direct images or arbitrary unbounded sources is added. |

The chosen universe convention is exactly that of the existing native framework, with arbitrary
`u`, not a specialization to small schemes. Every variable and universe is explicitly bound.
There are no file-local instances, notation, hidden statement `let`s, private definitions,
or supplemental postponed theorems.

Dependencies used, with their recorded declaration interfaces:

- `WeilConjectures.WeilSheaf.LowerShriek` publicly supplies the framework entry point and
  imports the actual `ProEtaleWeilSheaf`, `WeilComplex`, `WeilComplex.objectProperty`,
  `ProEtaleWeilSheaf.extensionByZero`, and `ProEtaleWeilSheaf.lowerStar`. Definitions read
  in `Category.lean`, `OpenImmersion.lean`, `LowerStar.lean`, and `LowerShriek.lean`;
  the coefficient definitions were checked in `Adic/ConstantSheaf.lean`, `Module.lean`,
  and `Constructible.lean`. `mapDerivedCategory` is termwise descent and
  `rightDerivedFunctor` is total native right derivation.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper` and its composition instance
  (the Mathlib match for proof dependency `lem-weil-pbc-proper-fp-permanence`).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` and its composition instance.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`: `IsPullback`, the
  universal-property formulation of the recorded fibre-product notion. Its cone is the
  pullback cone for the same pair `p,i` as `Limits.pullback` in the dependency record.
- `WeilConjectures.Compactification.RefinementCategory`: recorded
  `Compactification.Refinement` / `Compactification.category` and imported
  `Compactification` (its `Defs.lean` source read). The node defines F by its explicit
  factors, so there is no need to package those factors again as a compactification value.
- Proof-only `Sheaf.WeilSheaf.NativeBasicComparisons`:
  `AlgebraicGeometry.nativeWeilBasicComparisons`, parts (a) and (b), for pushforward and
  extension composition and preservation by J_s.
- Proof-only `Sheaf.WeilSheaf.NativeOpenProperInterchange`:
  `AlgebraicGeometry.WeilComplex.nonempty_extensionByZero_rightDerivedLowerStar_iso`.
  Its source is WC^der(U); substituting t,pW,p,i gives precisely the required comparison
  before precomposition with J_s and postcomposition with Rq_*.

Searches actually run:

1. `msearch.py`, leanfinder: “Native derived Weil sheaves compatible compactification tower
   proper pushforward open extension composition natural isomorphism”. Eight hits, including
   `Scheme.Modules.pushforwardComp`, sheaf pushforward composition, and
   `SheafOfModules.pushforwardComp`. They concern ordinary module sheaves or supplied
   continuous-site pushforwards; none gives this native bounded constructible tower calculation.
2. `msearch.py`, loogle: `"pushforwardComp"`. Twelve hits on presheaf/module-sheaf and
   scheme-module pushforward composition; no native Weil tower assertion. Read
   `SheafOfModules.pushforwardComp` in `PushforwardContinuous.lean` lines 127–143;
   it is an underived composition identification, not the present comparison.
3. `msearch.py`, grep: `compatibleTower|towerCalculation|rightDerivedLowerStarCompIso|extensionByZero.*[Cc]omp`
   in Mathlib `AlgebraicGeometry`: zero hits.
4. `rg -n` of that same expression in both `lean/WeilConjectures` and `lean/Sheaf` found
   the native direct-image composition in `WeilSheaf/FiniteLeray.lean`, existing open
   extension auxiliary comparisons, the two dependency modules, and an unrelated private
   integral coefficient tower comparison in `ConstantWeilStructure`. The full native
   direct-image composition signature/docstring was read (`FiniteLeray.lean` 159–177);
   it supplies only a comparison needed here, not the tower statement. No exact declaration
   exists. The upstream search by the exact node id returned no hits.

Edge cases checked before writing: all opens may be identities, reducing to direct-image
composition; s may have empty source, giving the unique zero-image comparison; an input
may be the zero complex or a shifted bounded constructible complex; open complements may
be empty or nonempty; the six schemes may be nonseparated over k₀. No nonempty-scheme,
positive-degree, absolute separatedness, nonzero-input, or bound on an intermediate direct
image occurs in the signature. The required prime/characteristic restriction is retained.
The proper/open step only uses J_s K with K bounded constructible, as required even if one
makes no assertion about any unbounded coefficient input.

Validation: prescribed `scompile.py` compiled the file separately as both a sandbox module
and its actual library module, in 5.5 and 4.0 seconds respectively, with no errors or
unexpected warnings. The only postponed proof is the named theorem above; its docstring
contains all five DAG proof steps and the dependency names. No statement dispute or node
correction was needed. No new nodes or dependency repairs were needed.

## Second reading by Q126

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
