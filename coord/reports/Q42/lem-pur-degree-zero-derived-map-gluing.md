## Worker report

Repair of the return against immutable head feffc6c59250. The retained sandbox contained
only dispatcher brief markers, with no Lean module, node record, or report. This delivery
supplies all three. The wrapper rebases the packet on the current newtargets-dag; no
shared source or repository was edited and no direct Git command was run.

Module: `Sheaf.Paper.DegreeZeroDerivedMapGluing`.
Primary declaration:
`AlgebraicGeometry.DegreeZeroMapGluing.degreeZeroDerivedMapGluing`.
The other four declarations belong to the same node: two actual canonical overlap
constructions and two predicates expanding the complete statement. No theorem other
than the main theorem is added. Its proof is `sorry`; all definition bodies are real
terms or explicitly written propositions.

The natural-language statement, stmt_deps, proof, and proof_deps are unchanged. No
new node or dependency replacement is needed. In particular
`def-pur-localized-ringed-site` is already a Mathlib leaf through its mathlib_match;
the absence of a lean record there does not mean the construction is missing.

Hypothesis and conclusion correspondence (all names below are in the primary namespace,
except the explicitly qualified library names):

| Node clause | Lean rendering |
| --- | --- |
| T is any scheme | `(T : Scheme.{u})` |
| Either the small etale or small pro-etale site | The theorem is the conjunction of two `Conclusion` instances: `Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A)` and `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u+1} A)`. No auxiliary abstract-site hypothesis occurs in the theorem. |
| Finite commutative ring, as constant coefficients | `(A : Type (u+1)) [CommRing A] [Finite A]`, and sheaves valued in `ModuleCat A`. Scalar actions by A correspond canonically to actions by the constant ring sheaf. No nontriviality, characteristic, flatness, or finiteness of the modules is imposed. |
| Ordinary derived categories of module sheaves | Each occurrence of `DerivedCategory (B X)` in the expanded `Conclusion` uses the actual sheaf category selected in the theorem. This is the established etale `DerivedCategoryModule` encoding. For pro-etale it is the fixed-ring presentation canonically identified with the recorded ring-sheaf category by `finiteCoefficientRealization`. |
| Cohomology sheaves | `DerivedCategory.homologyFunctor (B X) a`; this is homology of integer-indexed cochain complexes and hence ker(d^a)/im(d^(a-1)). |
| A set-indexed Zariski open cover | `{I : Type wI} (U : I → T.Opens) (hU : iSup U = ⊤)`. The index universe is independent and no nonemptiness is required. |
| Exact derived restriction to Ui | `(r (U i).ι).mapDerivedCategory`, with r instantiated to the existing `Etale.upperStar` or `ProEtale.upperStar` on A-module sheaves. Both are exact, and for open immersions coincide with localized-site restriction. These are concrete published functors, not arbitrary maps supplied by a hypothesis. |
| M,N in that category | `∀ M N : DerivedCategory (B T)` in `Conclusion`. |
| H^a(M|Ui)=H^a(N|Ui)=0 for a≠0 | The antecedent `∀ i, homologyConcentratedIn 0 0 (r_i.obj M) ∧ homologyConcentratedIn 0 0 (r_i.obj N)`. The existing definition is the conjunction of the standard t-structure bounds IsGE 0 and IsLE 0; `DerivedCategory.isGE_iff` and `isLE_iff` identify it exactly with the stated vanishing. |
| Global concentration for M and N | The first two consequents are `homologyConcentratedIn 0 0 M` and the same for N. |
| Canonical M ≅ H^0(M)[0] and N ≅ H^0(N)[0] | `HasCanonicalIdentifications` existentially gives e on all degree-zero objects of open subschemes of T. Taking `X=T`, `j=𝟙 T`, and the two preceding concentration proofs gives the required identifications. The target is the actual `DerivedCategory.singleFunctor (B X) 0` applied to H^0(K). |
| These are induced by good truncation | The final conjunct of `HasCanonicalIdentifications` quantifies over every representing complex K. It supplies the chain map `p : K.truncLE 0 ⟶ single(H^0 K)`, fixes p in degree zero to `K.truncLEXIsoCycles 0` followed by `K.homologyπ 0`, and fixes all other components to zero. It asserts `IsIso (Q.map (K.ιTruncLE 0))` and `IsIso (Q.map p)`, and the equation `Q(c) ≫ e.hom = Q(p) ≫ single.map(homologyFunctorFactors.inv)`. This specifies exactly the truncation roof Q(c)^(-1)Q(p), with the canonical representative/H^0 comparison. No splitting or arbitrary isomorphism replaces the roof. |
| Natural in the objects | The first conjunct of `HasCanonicalIdentifications` is `a ≫ e_L.hom = e_K.hom ≫ single.map(H^0.map a)` for every morphism between concentrated objects on an open subscheme. |
| Commutes with restriction | Its second conjunct is the restriction of e_K followed by the existing single-functor comparison and single applied to the existing cohomology comparison, equated to e of the restricted object. It quantifies over every further open immersion f into any open subscheme j of T, so includes identity and iterated restrictions. `_hf` and `hfj` are proofs of the open immersion properties, not extra geometric assumptions: their existence follows from the specified open immersions and composition. |
| Morphism agreement on Ui∩Uj | The compatibility condition is equality of `onSmallerOpen ... inf_le_left (a i)` and `onSmallerOpen ... inf_le_right (a j)` on `(U i ⊓ U j).toScheme`. |
| Correct identification of overlap endpoints | `openComp` derives the comparison from `upperStarComp`, `Functor.mapDerivedCategoryCompIso`, `mapDerivedCategoryNatIso`, and `Scheme.homOfLE_ι`. `onSmallerOpen` conjugates the restricted arrow by its inverse on M and its forward map on N. Thus both sides really lie in the same Hom set, rather than comparing arrows with merely isomorphic endpoints. |
| Restriction induces the displayed bijection | For EVERY family a, the formula in `Conclusion` says compatibility `↔ ∃! b : M ⟶ N, ∀ i, r_i.map b = a i`. This is bijectivity onto exactly the compatible families: the reverse implication includes compatibility of every restricted global map; the forward implication includes existence and uniqueness. It is not merely injectivity or a bijection with an unspecified set. |
| Under degree-zero identifications, this is sheaf-map gluing | `Function.Bijective (fun a : M ⟶ N ↦ (homologyFunctor _ 0).map a)` is followed by the restriction square for H^0 using `mapDerivedCategoryHomologyFunctorIso`. Combined with e's naturality, this says that conjugation by e sends a to `single.map (H^0.map a)`; fully faithful singleFunctor gives precisely the sheaf map. Hence the restriction bijection is the sheaf-map gluing bijection under these canonical identifications. |
| Equality can be checked on the cover | The last conjunct explicitly gives `(∀ i, r_i.map a = r_i.map b) ↔ a = b`. |
| Empty scheme and empty cover included | There is no `[Nonempty I]`, `[Nonempty T]`, positive-degree condition, or nonzero-ring condition. For I empty, `iSup U = ⊤` forces the empty scheme; compatibility and restriction equations are empty universal statements and the conclusion asserts the unique global arrow. |
| No claim of descent for arbitrary derived complexes | The gluing, H^0 bijection, and equality clauses are all after the local concentration antecedent. `HasCanonicalIdentifications` only addresses objects satisfying `homologyConcentratedIn 0 0`, also on the localized sites. |

Dependency interfaces read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`,
  including its full locally affine locally ringed-space definition.
- def-weil-pbc-etale-site: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `Scheme.smallEtaleTopology`, with `ofArrows_mem_smallEtaleTopology_iff` identifying
  jointly surjective covers.
- def-weil-pbc-proetale-site: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt`
  and `Scheme.ProEt.topology`. Its objects have universe u+1 and arrows universe u.
- def-weil-pbc-derived-categories: `WeilConjectures.AlgebraicGeometry.DerivedCategories`
  was read through `scompile.py --source`, since it is absent from the older local source
  checkout. Its public `Etale.DerivedCategoryModule A X` is definitionally
  `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A))`.
- def-weil-pbc-proetale-modules: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, read
  both locally and with `scompile.py --source`. `FiniteCoefficientModules` is modules
  over `finiteCoefficientRingSheaf`; `finiteCoefficientScalarMap_locallyBijective`
  identifies this coefficient sheaf with constant scalars. The canonical functor
  `finiteCoefficientRealization` and its `finiteCoefficientRealizationIsEquivalenceRing`
  identify the fixed-ring sheaf presentation used here with that module category.
  This is coefficient presentation, not replacement by condensed modules or by a
  bounded/constructible subcategory. Its exactness gives the induced equivalence of
  the ordinary derived categories. No extra topology is an input to this theorem:
  the finite ring has its specified discrete topology when applying that interface.
- def-weil-derived-cohomology-sheaves (Mathlib leaf): `DerivedCategory.homologyFunctor`
  and `homologyFunctorFactors` in `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- def-kun-truncations: public imports of
  `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`, supplying Mathlib's
  `CochainComplex.truncLE`, `ιTruncLE`, and `truncLEXIsoCycles`. Its recorded
  `IsSequentialHomotopyColimit` is the other part of that composite node and is not
  used in the present statement; the existing good truncations are used directly.
- def-pur-localized-ringed-site (Mathlib leaf): `GrothendieckTopology.over`,
  `Sheaf.over`, `SheafOfModules.overFunctor`, `overMap`, and `overFunctorMap`, from
  `Mathlib.CategoryTheory.Sites.Over` and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.
- lem-pur-site-restriction-module-adjunction-exact:
  `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`,
  `SheafOfModules.localizedModuleExactIndependent` and its restriction exactness
  instances, read with their independent site universes. They justify the site-local
  exact restriction used by the proof, without forcing u+1=u.
- lem-sf-exact-functor-derived-triangulated (Mathlib leaf):
  `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactors` and
  `mapDerivedCategorySingleFunctor` in
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

The concrete exact inverse images and their composition comparisons are
`Etale.upperStar`, `Etale.upperStarComp`, `ProEtale.upperStar`, and
`ProEtale.upperStarComp` from the corresponding published UpperLowerStar.Defs modules.
Their full signatures and construction by sheafification/Kan extension and adjunction
were read. The induced homology and composition comparisons are the existing ones in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

Available proof interfaces are imported, without public export where used only in the
proof: `Etale.overEquiv`; `Scheme.ProEt.weaklyEtale_localization`; constant-sheaf
restriction/continuous sheafification compatibility; `SiteCoveringAxioms`;
affine-open basis, affine quasi-compactness and quasi-separatedness; localized module
exactness; `DerivedCategory.truncation_descends`; localization universal property;
ringed module categories; full and faithful instances of `singleFunctor`; and
`SheafOfModules.existsUnique_hom_of_cover`. The seven-step proof in the theorem
docstring follows the node's seven proof steps, including the empty-cover sheaf axiom.

Searches made in this repair:

- msearch.py leanfinder: "Derived sheaf complexes locally concentrated in degree zero
  have uniquely gluable morphisms on a Zariski open cover". Eight hits, including
  `TopCat.Sheaf.existsUnique_gluing'`, `existsUnique_gluing`, unique-gluing sheaf
  conditions, and `Scheme.OpenCover.ext_elem`; none combines the local heart
  identification, ordinary derived maps, and both small sites. Read the returned
  signatures; they glue sections or scheme maps, not these derived arrows.
- msearch.py loogle: `DerivedCategory.singleFunctor`. Twelve hits, including
  `singleFunctor`, its Q comparison, Full/Faithful instances, and
  `singleFunctorCompHomologyFunctorIso`. Read FullyFaithful.lean and ExactFunctor.lean:
  these supply ingredients but do not state this open-cover result.
- msearch.py grep: `singleFunctor|glue|gluing` in Algebra/Homology/DerivedCategory.
  Twenty-five displayed hits, mainly Basic, TStructure and ExactFunctor; no full match.
- msearch.py leansearch: "Compatible morphisms between derived sheaves locally
  concentrated in degree zero glue uniquely". Eight hits for sheaf-section or scheme
  gluing; none is the requested derived gluing statement.
- rg for the exact node id in WeilConjectures: no declaration found.
- rg for `degreeZeroDerivedMapGluing|HasCanonicalIdentifications|onSmallerOpen` in
  Mathlib, WeilConjectures and lean/Sheaf: no existing declarations with these names.
- Read local derived singleFunctor/homology and t-structure source and project
  truncation interfaces. Reused `homologyConcentratedIn` instead of defining another
  concentration predicate.
- Read the cited Stacks passages in derived.tex (lemma-negative-exts),
  sites-modules.tex (lemma-internal-hom) and sites.tex (lemma-glue-maps).
  These give exactly the heart Hom identification and sheaf-map gluing route.

Edge cases checked before finalizing the statement: empty I; empty scheme; zero
coefficient ring; zero M or N; duplicated/redundant opens; empty intersections;
disconnected schemes; arbitrary unbounded representatives with cohomology only in degree
zero; degree zero versus every positive and negative degree; independent set-index universe;
and the pro-etale site's unequal object and Hom universes. No finite cover of T is
assumed (only affine refinements in the proof). No statement dispute or statement correction.

## Second reading by Q42

This is Q42's separate clause-by-clause rereading with the node and final file open;
the maintainer performs the independent review under the current direct-delivery workflow.
No second agent was started.

1. Reread the initial objects and hypotheses. Both site cases occur as actual
   instantiations in the final theorem. A is finite and commutative, I has arbitrary
   universe, and U is an open cover by `iSup U = ⊤`. M and N are arbitrary ordinary
   derived objects until the explicit local concentration hypothesis. There is no
   assumption of compactness, boundedness, constructibility, or nonempty indices.
2. Reread every vanishing clause against `Conclusion`: the two local concentration
   predicates exactly give the two off-zero vanishings; the next two conjuncts give
   the global vanishings. The established `homologyConcentratedIn` definition avoids
   replacing sheaf vanishing by vanishing merely of global sections.
3. Reread the canonical-isomorphism clause against `HasCanonicalIdentifications`.
   An unspecified existential isomorphism alone would omit the requested
   good-truncation construction. The delivered formula instead fixes the roof,
   the quotient map on cycles in degree zero, the zero components in other degrees,
   and invertibility of both legs. It uses the inverse of `homologyFunctorFactors`
   in the required direction from representative H^0 to derived H^0. No data is sorry.
4. Reread naturality and restriction. The first equation has type
   `K ⟶ single(H^0 L)` on both sides; the second uses the hom direction of the
   single comparison followed by the hom direction of the H^0 comparison. It
   includes all further open immersions, hence identity and repeated restrictions.
5. Reread overlap compatibility. Raw restrictions on an intersection have differently
   presented endpoints. The delivered `onSmallerOpen` explicitly transports by
   `openComp.inv.app M` and `openComp.hom.app N`; `openComp` includes the equation
   `homOfLE ≫ ι = ι`. Both compared maps therefore have the actual same endpoints
   over Ui∩Uj. This fixes the endpoint-identification issue rather than asserting
   equality with heterogeneous or arbitrary restriction maps.
6. Reread bijectivity. Compatibility iff `∃!` a global map with the specified
   restrictions gives BOTH surjectivity and injectivity and ensures compatibility
   of each restricted global map. This is precisely the displayed subtype bijection.
7. Reread the identification with module-sheaf gluing: the global H^0 Hom map is
   bijective, e is natural, and the exact-restriction H^0 square commutes. Thus the
   global map corresponds to its sheaf map, and local agreement is the corresponding
   sheaf agreement. The explicit final iff is the node's equality check.
8. Reread the empty-case sentence. No binder excludes it; on an empty cover the
   compatibility condition is vacuous while unique existence remains asserted.
   Concentration is still the hypothesis for all nonempty-cover gluing claims.
9. Reread dependency interfaces: the localized-site node already has the exact
   Mathlib match, the truncation node reexports the actual good truncations, and
   fixed-ring pro-etale modules have the canonical recorded coefficient realization.
   No missing definition, duplicate concentration predicate, arbitrary canonical map,
   or forced universe equality was introduced.

Repairs to the numbered return: H2/H3 are addressed by the full formal statement and
complete lean record; H1/H11 by this Worker report and the concrete second reading.
The initial parser issue in the function type returning an isomorphism was fixed by
parenthesizing that isomorphism; this did not change the mathematical statement.

## Compilation evidence

All compilation uses the prescribed wrapper with group Q42 and item
lem-pur-degree-zero-derived-map-gluing, and the sole delivered file
`lean/Sheaf/Paper/DegreeZeroDerivedMapGluing.lean`. No global build was run.

The first clean scompile.py run reported separate sandbox and library validation:

```
sandbox Sheaf/Stage2/Sandbox0.lean
(with the modules compiled into the private overlay) [15.8 s]
library Sheaf/Paper/DegreeZeroDerivedMapGluing.lean
[25.4 s]
```

No errors or warnings. After adding all available proof-dependency imports the final
file is compiled again; final evidence and delivery dry-run results are appended below.

Final-file scompile.py result (all proof imports present): exit 0, no errors or warnings.
The wrapper reported sandbox validation in 13.0 s and separate library validation in
56.1 s, each under the unchanged 60 s per-file limit with the private overlay. The
imports of the recorded coefficient module and upstream derived-category module
coexist cleanly on the current published sources; no dependency-record repair was needed.

Delivery dry run: `deliver2.py Q42 lem-pur-degree-zero-derived-map-gluing --no-push`
returned exit 0 and:
`OK (dry run): commit e515f3552e passes the preflight and compiles; nothing pushed`.
The exact staged set was the item's node JSON, this report, and the single Lean module.
A local field comparison confirms that only `lean` changes in the node; the signature
is verbatim, all source lines are within 100 characters, and the only sorry is the
main named theorem. The push reruns compilation and preflight on the final packet.
