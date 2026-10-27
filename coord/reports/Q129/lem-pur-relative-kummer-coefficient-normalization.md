## Worker report

The module `Sheaf.Paper.RelativeKummerCoefficientNormalization` states
`WeilConjectures.PurityFiniteSetting.relativeKummerCoefficientNormalization`, with
one `sorry`. Its complete eight-step proof is in the theorem docstring. The supporting
maps have actual definitions, built from published constructions. No definition data
is postponed. The node statement, proof and proof dependencies are unchanged.
Statement dependencies name the existing canonical trivialization and omit the
strict-local theorem.

The source read was the current blueprint under `literature/blueprint/latest/`,
`sec-six-functors-basics/sk-prop-a1-kummer/prop-pur-gm-relative-kummer.proof.md`,
opening paragraph and Step 3. Stacks 03PL was read in
`literature/stacks-project/etale-cohomology.tex`, lemma-kummer-sequence (lines 2842ff).
This is the ordinary abelian Kummer sequence on an arbitrary scheme, before scalar
extension.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Fixed finite-field and coefficient datum, including n >= 1 | `P : PurityFiniteSetting.{u}`; the fields of the recorded structure contain the finite field, algebraic closure, ell distinct from p, finite coefficient extension, level and `level_pos`. `P.Coefficient` is the standard ULift of the actual quotient `P.Ring`. |
| e divides n; N=n/e; r=ell^N; R=Z/r | `h : P.ramificationIndex ∣ P.level`; existing `P.kummerLevel`, `P.exponent`, and `ZMod P.exponent`. The first conclusion is `1 ≤ P.kummerLevel`; no positivity assumption was added. |
| rA=0 | `(P.exponent : P.Coefficient) = 0`. In a unital ring this is exactly annihilation of every element by r. |
| A finite free R-algebra | A ring homomorphism `α : ZMod P.exponent →+* P.Coefficient`, a finite rank d and an additive equivalence b to `Fin d → ZMod P.exponent`, with `b (α z * x) = z • b x` for every z and x. This is precisely an R-linear basis presentation; the scalar map from ZMod is unique, so no arbitrary coefficient action is substituted. |
| r invertible on every k-scheme | Every `T : Over (Spec (.of P.field.k))` satisfies `IsUnit (P.exponent : Γ(T.left, ⊤))`. There are no finite-type, reducedness, connectedness, or qcqs hypotheses. |
| Choose primitive r-th root zeta in k | Universal quantification over `ζ : P.field.k` with `IsPrimitiveRoot ζ P.exponent`; the conclusions hold for every such choice. Existence comes from the algebraically closed field in P and the cited primitive-root lemma. |
| R_T isomorphic to mu_r,T, a maps to zeta^a | The existing `T.left.constantZModIsoRootsOfUnitySheaf P.exponent T.hom hζ`, of type `T.left.constantZMod P.exponent ≅ T.left.rootsOfUnitySheaf P.exponent`. Its normalization is tested after `kernel.ι` on every sheafified constant natural-number label b over every etale test W, where its value is the restriction of zeta raised to b. Natural labels exhaust ZMod. The unique ZMod action on exponent-r groups makes this abelian-sheaf isomorphism R-linear as well. |
| A_T isomorphic to L_T, a maps to zeta tensor a | `τ T : P.constantEtale T.left ≅ P.twistEtale h T.left`, with the displayed equality on every sheafified constant coefficient a at every W. The right side is the existing `finiteEtaleTateOneGenerator` evaluated on the root `θ(1)`. Here θ denotes that existing canonical root isomorphism. The published scalar extension writes `a tensor zeta`; the symmetry identifies this with `zeta tensor a`. |
| Both isomorphisms compatible with every k-morphism | The two equations quantified over `v : T' ⟶ T` in `Over (Spec k)`, using `upperStarConstantSheafIso`, `relativeRootPullback` and `relativeTwistPullback`. These last two are direct specializations of the recorded `finiteEtaleTwistPullbackData.r` and `.c`; their kernel and pure-tensor normalizations are retained. |
| L_T pulled back from Spec k | The natural isomorphism family includes the object `Over.mk (𝟙 (Spec k))` and every structure arrow `T.hom`. Specializing its naturality equation gives exactly this canonical pullback identification, rather than imposing it as a hypothesis or choosing an unrelated line. |
| Underlying finite coefficient group has ell-power order | `∃ d : ℕ, Nat.card P.Coefficient = P.coefficients.l ^ d`. This positive cardinality implies finiteness; τ identifies the underlying coefficient group with this additive group. It does not assert that global sections on a disconnected scheme have finite cardinality. |
| Define kappa by ordinary boundary, then coefficient insertion | The formula is written directly: `Sheaf.H.map (ordinaryFiniteRootMap P.Coefficient P.exponent (P.exponent_coefficient_eq_zero h) T) 1 (T.kummerδ₀ P.exponent (P.exponent_isUnit T a) (Additive.ofMul w))`. It uses only the recorded ordinary root insertion and abelian Kummer boundary. |
| Pullback of kappa(v) equals kappa(pullback v) | The all-unit equation uses the prescribed `cohomologyMap`, followed by `Sheaf.H.map` of `moduleAbelianUpperStarComparison` composed with forgotten `relativeTwistPullback`. Its right side uses `Units.map v.appTop.hom.toMonoidHom`. The source structure on T' is the composite with the structure of T. |
| No R-module action on G_m | The Kummer boundary above lives in abelian sheaves; only its target is mapped by `ordinaryFiniteRootMap`. No Module instance or module-valued G_m occurs anywhere. |
| Constants and coefficient maps unchanged by forgetting | The equation for `constantCommuteCompose` on sheafified constant sections a fixes the constant comparison. The separate equation for `ordinaryFiniteRootMap` at every root z identifies its underlying map with `finiteEtaleTateOneGenerator ... 1 z`, so no automorphism of the coefficient line can modify the insertion. |
| Canonical global comparison in all integer degrees | `relativeGlobalSectionsForgetIso` is fixed by evaluation at the terminal object. `relativeDerivedGlobalForget` is `rightDerivedFunctorPlusBaseChange` of this exact square. `relativeGlobalForgetMap T q K` is its homology map composed with the exact coefficient-forgetting homology comparison, for arbitrary `q : ℤ`. The theorem asserts invertibility of both this derived transformation and every homology map. Specializing K to F[0] gives exactly the underlying groups of H^q(X,F). |
| Canonical higher-direct-image comparison in all integer degrees | `relativeHigherForgetIso a q F` has exactly source `U_B(R^q a_* F)` and target `H^q(Ra_* (U_X F)[0])`. Its data is the composite of `mapDerivedCategoryPlusHomologyFunctorIso`, the component of `moduleAbelianDerivedLowerStarIso`, and `mapDerivedCategoryPlusSingleFunctor`. The theorem additionally records invertibility of the actual derived direct-image transformation. No existential selection of an isomorphism is used. |
| Coefficient and resolution-induced maps agree | The global comparison is a natural transformation, not a family of selected isomorphisms; its naturality identifies every coefficient morphism and every map in D+ represented by a resolution lift. The higher comparison is composed from components of the published natural isomorphisms, so it has the same naturality. Derived descent is the actual right-derived unit construction; its factorization on complexes fixes the representative Gamma(I) to Gamma(J), respectively a_* UI to a_* J. |
| Cohomology pullbacks agree | The explicit derived equality intertwines `moduleDerivedCohomologyPullback` with `abelianDerivedCohomologyPullback`, through `relativeDerivedGlobalForget` and `moduleAbelianDerivedUpperStarIso`. Applying H^q gives the required equality in each integer degree, with precisely the canonical inverse-image comparison. |
| Every cartesian square: actual exchange maps agree | Quantification over `ChosenCartesianSquare g' f' f g` and K, followed by the equality involving the actual `derivedBaseChangeMapPlus`, `moduleAbelianDerivedExchangeSourceIso` and `...TargetIso`. The adjacent equivalence is invertibility of the module exchange iff invertibility of the abelian exchange. |
| Forgetting reflects invertibility | The last two clauses quantify over all module-sheaf maps and all bounded-below module-derived maps and assert `IsIso (forget.map b) ↔ IsIso b`. No invertibility is assumed. |

Dependency declarations used (all recorded signatures and docstrings read):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Coefficient`, `.constantEtale`, `.twistEtale`, `.forgetEtale`,
  `.exponent_coefficient_eq_zero`, `.exponent_isUnit`.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`:
  `AlgebraicGeometry.Scheme.kummerSequence`, `.rootsOfUnitySheaf`, `.constantZMod`,
  `.kummerδ₀`, `.kummerSequence_shortExact`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the existing general sheaf tensor interface.
  The concrete root line is the published sheafified extension of scalars, not a new tensor.
- `Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback`:
  `AlgebraicGeometry.Etale.cohomologyMap`, `.moduleDerivedCohomologyPullback`,
  `.abelianDerivedCohomologyPullback`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the existing small-etale sheaf
  categories. `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, also its existing Plus restriction.
- `WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget`:
  `AlgebraicGeometry.Scheme.nonempty_etaleModuleCohomology_forgetIso`. Its proof's
  evaluation square fixes the comparison used here; an arbitrary witness is not chosen.
- `WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison`:
  `AlgebraicGeometry.Etale.nonempty_higherDirectImage_forget_iso`; its canonical
  composite is named `relativeHigherForgetIso` in this delivery.
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`:
  `AlgebraicGeometry.Etale.exchange_forget_coefficients`, and its publicly imported
  `moduleAbelianDerivedLowerStarComparison`, `moduleAbelianDerivedLowerStarIso`,
  `moduleAbelianUpperStarComparison`, `moduleAbelianDerivedUpperStarIso`, and the
  source/target exchange comparison isomorphisms.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `AlgebraicGeometry.Scheme.finiteEtaleTwistPullbackData`, with `.r` and `.c`.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`:
  `AlgebraicGeometry.Etale.ordinaryFiniteRootMap`; the imported finite twist source
  supplies `AlgebraicGeometry.Scheme.finiteEtaleTateOneGenerator`.
- `WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity`:
  `AlgebraicGeometry.Scheme.constantZModIsoRootsOfUnitySheaf`, the declaration of
  `def-sc-mu-trivialization`. Its complete signature and docstring were reread:
  it accepts any scheme over a field, a nonzero exponent and a primitive root.

The added landed statement dependencies are `lem-asd-etale-finite-twist-pullback`,
`def-asd-ordinary-finite-p1-kummer-class` and `def-sc-mu-trivialization`.
The strict-local theorem node and its import have been dropped, as requested by H2.
No new node, dependency repair or mathematical statement correction is needed.

The named instance `relativeExponentNeZero` packages `pow_ne_zero` and the existing
primality of ell, enabling the canonical root-trivialization API without a new hypothesis.

The named instance `relativeScalarForgetFiniteColimits` packages Mathlib's existing
`ModuleCat.forget₂PreservesColimitsOfShape.{u+1,u+1,0,0}` for the finite diagram shapes.
This fixes an elaborator universe ambiguity in the generic `PreservesColimits` search;
it introduces no mathematical assumption and does not identify distinct site universes.
The category of schemes remains at u, its etale objects at u+1 and arrows at u, and
module/abelian carriers at u+1. There are no file-local notations or instances.

Edge cases checked before finalizing:

- T empty: the sheaf and constant comparisons are still isomorphisms; no test requires
  the image of the primitive root to remain primitive in the zero ring of sections.
- T disconnected, including an infinite disjoint union: the assertion concerns the
  finite coefficient group A, not the group of all global sections.
- T nonreduced, such as Spec k[epsilon]/epsilon^2: the root sheaf is the actual kernel;
  the factorization/local-unit argument in the docstring applies without reducedness.
- n=e gives N=1. The statement adds no N>1 or unramified-extension assumption.
- Ell=2 and ramified E are permitted. Only ell != p from P is used for invertibility.
- Degree zero and every negative integer q remain in `relativeGlobalForgetMap` and
  `relativeHigherForgetIso`. No natural-number truncation is introduced.
- Identity morphisms, arbitrary k-morphisms, and identity cartesian squares remain
  quantified over. No etaleness, smoothness or properness is added to these arrows.
- The zero ring is not a new coefficient case in the fixed positive finite quotient
  datum, but the canonical forget and derived comparison constructors retain their
  existing zero-ring behavior without a Nontrivial assumption.

Searches, through the prescribed msearch.py wrapper and read-only source search:

1. LeanFinder: "Primitive root trivialization of etale Kummer coefficients natural
   under pullback and compatible with forgetting module scalars". Eight hits, headed
   by `StandardEtalePair.HasMap.map`; no statement matching this node.
2. Loogle: `IsPrimitiveRoot, ZMod`. Twelve hits, including
   `IsPrimitiveRoot.zmodEquivZPowers`; these are group/ring results, not this normalized
   sheaf/cohomology assertion.
3. Mathlib grep: `kummer|rootsOfUnity.*Sheaf|cohomology.*forget`. Twenty-five displayed
   hits, mostly number-theoretic Kummer results; no match for the whole statement.
4. LeanSearch: "Primitive roots trivialize etale roots of unity sheaves naturally
   under pullback, and Kummer boundary classes commute with scalar extension".
   Eight hits on primitive roots, including `IsPrimitiveRoot.map_rootsOfUnity`;
   no full assertion on the specified etale coefficient comparisons.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node id, normalization name,
   Kummer naturality, root trivialization and coefficient-forgetting comparisons.
   Existing root maps and exchange comparisons were read and reused. A further
   concept search located the existing `Etale.relativeKummerClass`; the H2 repair
   now spells its boundary-and-insertion composite directly, without importing it.
   `RootsOfUnityPullback` treats ordinary root cohomology and its higher boundary, not this complete statement.

Validation: the prescribed scompile.py compiled the module in sandbox and at its
library module name without errors or non-sorry warnings. No local/global Lean build,
Git command or direct edit was run in the shared read-only repository.

No STATEMENT-DISPUTED issue was found.

## Second reading by Q129

This is a separate final reading by the assigned worker; no additional agent was
started, as the dispatch explicitly forbids it. The maintainer supplies the independent
review after delivery. I reread the node, source, complete final Lean file and every
row of the clause correspondence above.

The original reading found and corrected the following issues before delivery: the exponent
invertibility declaration takes the scheme as an explicit argument; finite-colimit
instance search needed its carrier universes fixed; the first draft's root-value
coercion had one incorrect parenthesis; and the exact existing `Etale.relativeKummerClass`
was found in a second source search and reused instead of repeating its construction.
The final reading also added the explicit constant-section normalization equation.

The final field/level assumptions are exactly P and e|n. The R-linear basis assertion
is expressed without adding an arbitrary action. The root trivialization is the published
`Scheme.constantZModIsoRootsOfUnitySheaf`, and its formula is asserted on every constant
label; τ is fixed by every pure coefficient, and their naturality uses canonical maps.
All scalar-forgetting comparisons have fixed data, the Kummer pullback uses the
recorded abelian convention, and the exchange equation mentions the actual derived
mate. Every source clause has the rendering listed above. No source correction,
new definition node or dependency-module repair remains outstanding.

## Returned review repaired

The saved packet was first checked with the required `deliver2.py --no-push`.
That produced dry-run commit `1012c819460` and passed the mechanical preflight;
it still contained both issues identified in independent head `5c4e19283f73`.
The following are substantive repairs of those issues.

- H2: chose the reviewer's explicit inline alternative. Both occurrences of kappa
  now spell `Sheaf.H.map (ordinaryFiniteRootMap ...) 1 (T.kummerδ₀ ... (Additive.ofMul w))`,
  including the pulled-back unit on T'. Removed both the statement dependency
  `lem-pur-relative-kummer-strict-local-invariance` and its module import. No
  `relativeKummerClass` or `relativeKummerMapOnCohomology` is used. Accordingly no
  additional ownership node is needed. The genuine `lem-asd-etale-finite-twist-pullback`
  dependency and its canonical chosen data remain, as the reviewer passed them.
- H4: removed the existential theta. Every root value, the tensor generator and the
  root naturality equation now use `Scheme.constantZModIsoRootsOfUnitySheaf` directly,
  with the structure arrow T.hom and the bound primitive-root proof hζ. Added its
  existing owner `def-sc-mu-trivialization` to stmt_deps and made its import public.
  The nonzero-exponent instance is computed from `pow_ne_zero` and ell's primality;
  it adds no assumption, even if the level were zero. Tau remains the asserted
  scalar-extension trivialization normalized by that same canonical root map.

Second reading of the repair: compared the saved packet with current main's node
(no Lean record there; original nine statement dependencies) and the returned head
as described in the return. Reread the updated theorem, the canonical root-isomorphism
signature and construction, and the boundary definition. The unchanged clause table
above applies with canonical theta throughout. The kappa formula is now literal,
so it neither assumes strict-local invariance nor uses its theorem as a definition.
The source's arbitrary k-schemes, every k-morphism, all integer degrees, and all
exchange/reflection clauses are retained. Rechecked empty, disconnected and nonreduced
schemes, n=e, ell=2 and negative degrees: the repairs introduce no new restriction.
A read-only search in WeilConjectures, Sheaf and the DAG confirmed the existing
root-trivialization owner and found no competing `relativeExponentNeZero` declaration.
No source correction, new definition node or dependency-module repair is outstanding.
