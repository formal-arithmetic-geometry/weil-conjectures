## Worker report

The delivery states `closedSupport_stratum_globalHom` in
`Sheaf.AlgebraicGeometry.ClosedSupportStratumHom`, with two new definition nodes.
The original item statement is unchanged. Every theorem proof is `sorry`; definitions
have actual construction data. No statement dispute or counterexample was found.

The source read was the complete current blueprint leaf
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sf-localization/sk-lem-formal-closed-support-stratum-hom.md`,
together with the DAG's expanded statement and five proof steps. The quasi-compact
complement hypothesis is retained exactly as already present in the reviewed DAG.

Clause-by-clause rendering:

| Natural statement | Lean |
| --- | --- |
| Commutative condensed ring | `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}`, `[MonObj Λ]`, `[IsCommMonObj Λ]` |
| Admissible coefficient family, including finite ell-power torsion, Z_l, O_E, Q_l, E, Qbar_l | `_hΛ : IsAdmissibleCoefficient Λ`; the definition uses ring-object isomorphisms to the existing continuous-map and finite-subextension models |
| Pulled-back coefficients Λ_T on small pro-etale sites | `supportModules Λ T`, definitionally `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u+1}) (condensedRingObj Λ T)` |
| Size convention | Explicit `universe u`; site objects in `Type (u+1)` and site arrows in `Type u`, module Hom and abelian groups in `Type (u+1)`; Grothendieck-derived localization in the existing framework |
| Closed i: Z -> X | `(i : Z ⟶ X) [IsClosedImmersion i]` |
| Complementary quasi-compact open j | `(j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]`, with `hij : Set.range i.base = (Set.range j.base)ᶜ` |
| Open u: S -> Z | `(uS : S ⟶ Z) [IsOpenImmersion uS]` |
| a=i o u, a!=i*u! | The argument of the first RHom is literally `(lowerStar Λ i).obj ((openImmersionLowerShriek Λ uS).obj L)`; no separately chosen a! or exceptional proper adjoint |
| Gamma_Z=i*ker(id -> j*j*) | The imported actual `closedSupport Λ i j`, defined from `supportKernel` and `supportPullback` |
| Unbounded right derived R-Gamma_Z | `(closedSupport Λ i j).rightDerivedFunctor` |
| Finite locally projective L on every site object, with covering-dependent finite ranks | `(L : supportModules Λ S) (hL : IsFiniteLocallyProjective Λ S L)`; every site object gets a covering sieve, and every domain has explicit retraction maps to/from `Mod.finiteFree` |
| L-dual=sheafHom(L,Λ_S) | `stratumDual Λ S L := (ihom L).obj (𝟙_ (supportModules Λ S))`; the existing module monoidal closed structure represents the coefficient-linear sheaf Hom, and its unit is `Mod.regular` |
| Ordinary unbounded derived categories, L in degree zero | `DerivedCategory (supportModules Λ T)` throughout; `stratumGlobalRHom` derives Hom from a module, and the last clause explicitly uses `DerivedCategory.singleFunctor ... 0` |
| Global RHom computed into K-injectives | `stratumGlobalRHom Λ T M := (preadditiveCoyoneda.obj (op M)).rightDerivedFunctor`; its K-injective model has terms `Hom(M,I.X n)` and postcomposition differential |
| H^q=H^q R-Gamma | `stratumRGamma` derives Hom from the regular coefficient module, and `DerivedCategory.homologyFunctor Ab.{u+1} q` takes degree q |
| First displayed comparison | First `Nonempty` natural isomorphism, from RHom_X(i*u!L,-) to R-Gamma_Z followed by RHom_Z(u!L,-) |
| Second displayed comparison | Second `Nonempty` natural isomorphism, adding exact `(upperStar Λ uS).mapDerivedCategory` and RHom_S(L,-) |
| Third displayed comparison | Third `Nonempty` natural isomorphism, replacing RHom_S(L,-) by `stratumDualTensor ... ⋙ stratumRGamma ...` |
| Tensor computed termwise | `stratumDualTensor` is the exact functor `tensorLeft (stratumDual ...)` descended by `mapDerivedCategory`; `stratumDualTensor_preservesFiniteLimits` states the needed exactness |
| It agrees with derived tensor | `stratumDualTensor_derived` compares that functor with the existing `derivedTensor` applied to L-dual in degree zero |
| Naturality in every K | Each comparison is a natural isomorphism of functors on the whole source `DerivedCategory`; there is no boundedness, completeness or constructibility predicate |
| In particular, every integer q | Final `∀ q : ℤ, Nonempty (...)` compares shifted preadditive coyoneda from a!L[0] with the degree-q homology of the displayed R-Gamma functor; both are abelian-group-valued functors, so this includes naturality |

The following recorded dependency declarations were read in full with their docstrings:

- `Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction`: `supportModules`,
  `supportPullback`, `supportKernel`, `closedSupport`, `closedSupport_globalRHom`,
  `closedSupportDerivedAdjunction` and the rest of the recorded clause declarations.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, `coefficientPullbackIso`, `isIso_condensedPullbackHom`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `openImmersionLowerShriek`, exactness and `openImmersionLowerShriekUpperStarAdjunction`.
  Its unbounded exact derived interface is imported from
  `...Derived.OpenImmersionLowerShriek`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `Q` and `singleFunctor`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`: `homObj`
  and `homObjSectionsEquiv`, the actual sheaf Hom interpretation.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal`, the recorded sheafified relative tensor.
- `Sheaf.Algebra.Homology.HomComplex`: `homComplex` and `homComplexFunctor`,
  the degreewise product/differential interpretation.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  `ringedSiteZerothHypercohomologyOfUniverses`, H0 composed with derived Hom from the unit.

The last four ringed-site dependencies are publicly imported; their coefficient-module
notions are used through the existing upstream module-object presentation, rather than
copied as new sheaf constructions. In particular the ordinary module `ihom` and relative
tensor are exactly the existing closed monoidal module operations. Global RHom is the
right derived *global* Hom functor, and is not the upstream derived internal Hom.
`stratumRGamma` is its unit specialization, the same Hom-from-the-coefficient-unit
construction as the recorded hypercohomology definition. There is no separately assumed
Hom functor, tensor, comparison map or resolution. The ordinary support definition uses
restriction of scalars through alpha inverse, whereas the open adjunction's `upperStar`
uses scalar extension through alpha; both are the existing canonical inverse images
through the same invertible coefficient comparison.

Proof dependency modules are imported without `public` when they are used only by the
proof plan. Recorded upstream-closed dependencies without `lean` records use their
`lean_audit.slopmaster2.decls`: the ordinary open adjunction and cartesian coefficient
comparison are already supplied by the imported framework. The K-injective Hom comparison
is Mathlib's `CochainComplex.IsKInjective.Qh_map_bijective`.

Edge cases checked: S, Z, X or the complementary open may be empty; no nonemptiness
hypothesis occurs. Rank zero is allowed by `r : ℕ`, and the local ranks need not be
constant. The zero coefficient ring is allowed (a finite ring with l^0=0); no nontrivial
ring assumption occurs. Identity open/closed immersions are allowed. Every q, positive,
zero or negative, is quantified as an integer. The source and target complexes may be
unbounded in either direction. No relation between site object and arrow universes
has been imposed. Finite rings and finite extensions are represented by small isomorphic
models, which loses no finite ring or finite-dimensional extension.

Searches made before writing: msearch LeanFinder on the complete derived stratum-Hom
formula returned ordinary scheme restriction adjunctions only; msearch Loogle on
`CategoryTheory.Adjunction.homEquiv, SheafOfModules.homObj` rejected the latter unknown
name, so that query is not absence evidence. A valid Loogle query on
`Module.Finite.exists_comp_eq_id_of_projective` returned the ordinary algebra retraction
lemma only. msearch grep on `FiniteLocallyProjective|finiteLocallyProjective|stratumHom|globalRHom`
returned zero matches. LeanSearch on local finite projectivity returned ordinary module
retractions, free sheaves and finite-presentation declarations, none defining the local
predicate. LeanFinder and LeanSearch on the admissible condensed coefficient family
returned padic rings and condensed modules, no family predicate. Regex searches of
upstream `WeilConjectures/`, shared `lean/Sheaf/`, `dag/lean_names_upstream.json` and
`dag/nodes/` found no named predicates and no complete matching theorem. Searching the
item id upstream found no declaration. `blueprint_refs.py search 'finite locally projective'`
found two consumer blueprint nodes; `search 'admissible condensed'` found none. The
similar basics stratum node has no Lean declaration and carries different standing
hypotheses, so it cannot be bound as an existing theorem. Search outputs are recorded
verbatim in the new nodes' `mathlib_searches` where applicable.

## New nodes

`def-pur-condensed-finite-locally-projective` defines precisely local retractions of
finite free pulled-back coefficient modules on covering sieves of every site object.
Its source is the opening finite locally projective hypothesis of this blueprint leaf.
The LeanSearch, valid Loogle and Mathlib/upstream/shared/DAG searches above found only
ordinary algebra retractions and consumers. `Mod.finiteFree` and the canonical
`supportPullback` are reused. No new module category or restriction is introduced.

`def-pur-admissible-condensed-ring` defines membership, up to ring-object isomorphism,
in the coefficient family explicitly listed by the item. It uses the existing
continuous-map condensed ring construction for finite discrete rings, Z_l, Q_l and
finite subfields, the existing integer-ring model for O_E, and the existing
finite-subextension-valued Qbar_l construction. Its source is the same opening
coefficient hypothesis. LeanSearch, LeanFinder and grep found constituent rings but
no predicate for this finite list. The definition is real propositional data with
no postponed construction. It includes arbitrary finite extensions through their
embeddings into the fixed algebraic closure; all such extensions admit these models.

## Second reading by Q20

This is the author's second reading; the maintainer performs the independent review,
as the dispatch brief specifies. I reopened the node and all three modules and matched
all hypotheses and all displayed clauses in the table above. The first reading caught
and repaired the `FiniteIntermediateField` namespace (`PadicAlgCl`, not `Profinite`).
The compiler also required exact tensor to supply preservation of finite limits explicitly;
I changed the helper from preservation of homology to `PreservesFiniteLimits`, while
tensor already preserves finite colimits. The derived functor is global Hom into abelian groups, not an
internal Hom on X. The final clause puts q on K on the left and degree q on the right,
with no sign reversal. It includes every integer. The a! argument is the specified
closed pushforward after open extension, in that order. The complement condition and
quasi-compactness have both been retained. All three comparisons are functor
isomorphisms, which explicitly enforces the required naturality. The additional tensor
lemma makes the termwise/derived agreement explicit. I found no need to correct the
item's natural-language statement.

Validation: the final three-file `scompile.py` run exited 0 with no warnings or errors.
The library checks took 22.7 s for the coefficient family, 5.0 s for finite local
projectivity, and 18.4 s for the full Hom module, each under the prescribed limit.
The definitions contain no sorry; the three named theorem proofs are the stage-2 sorries.

Server preflight required the new nodes to use the blueprint leaf ancestry with
`blueprint.from.via = []`; both ancestry fields were corrected. No Lean file or
mathematical statement changed in that metadata repair.
