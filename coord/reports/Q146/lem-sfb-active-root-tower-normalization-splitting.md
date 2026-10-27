## Worker report

The module `Sheaf.RingTheory.ActiveRootTowerNormalizationSplitting` states
`Algebra.ActiveRootNormalization.activeRootTower_normalization_splitting` with
one postponed proof. Its other declarations construct the particular algebras,
closures, inclusions and diagrams used in that statement. No theorem is proved,
no data is postponed, and no statement correction is made.

### Rendering of the hypotheses

- The positive prime is `p : ℕ` with `hp : p.Prime`. The coefficient ring is
  `B : Type u`, `[CommRing B]`, `[Algebra (ZMod p) B]`, `[IsNoetherianRing B]`.
  This permits the zero algebra; the chosen geometric point then makes that case
  vacuous, just as in the node.
- `r : ℕ` and `t : Fin r → B` give exactly the finite labelled parameter list.
  The product `∏ i, t i` is always the full boundary product, with value 1 at r=0.
  `hf` is injectivity of multiplication by this product, not nonvanishing or a
  domain hypothesis.
- `Algebra.pthRootAlgebra m r B t` is the already recorded multivariate quotient
  C_m for any exponent m. `hnormal` quantifies over every positive prime-to-p
  exponent and every prime ideal q, requiring both `IsDomain (Localization.AtPrime q)`
  and `IsIntegrallyClosed (Localization.AtPrime q)`. No global domain condition
  is substituted for normality.
- `D : Under (.of (Localization.Away (∏ i, t i)))` retains the algebra and its
  structural map. `hfinite : D.hom.hom.Finite` and `hetale : D.hom.hom.Etale`
  are the finite and etale algebra hypotheses, in the affine form used in the node.
- `Ω`, `[Field Ω]`, `[IsAlgClosed Ω]`, and `v : Spec Ω ⟶ Spec B` are the
  geometric point. Its image is `v (IsLocalRing.closedPoint Ω)` and its ideal
  is `.asIdeal`.
- `A`, its commutative B-algebra structure, `e : Spec A ≅
  Scheme.strictHenselizationScheme v`, and `he` present the specified strict
  localization with exactly its structural B-map. The recorded geometric
  strict-henselization construction and structural map are used, rather than
  identifying two distinct APIs definitionally. The affine-chart proof tool
  uses `strictLocalization`; its canonical comparison with this small
  representative model is supplied upstream by `StrictHenselizationExtension`.
  The abstract pointed-etale presentation in the original dependency remains
  imported; no competing strict henselization is constructed.
- `active : Fin s ↪ Fin r` enumerates the active subset. `hactive` says its
  image is exactly the labels whose parameters belong to the image-point prime.
  An arbitrary finite subset has such an enumeration, including the empty set;
  this introduces no boundary restriction or chosen roots.
- `rootDiagram` reuses `simultaneousRootDiagram` and its power transitions,
  restricted to `RootTowerIndex {n : ℕ+ | Nat.Coprime (n : ℕ) p}`. The order
  here is the recorded divisibility preorder, not the ordinary numerical order.
- `activeDiagram` first uses the existing root quotient for the active parameter
  family over A, restricts coefficients along B→A, then pushes out along
  B→B[1/f]. Thus its stage is precisely T_m[1/f], with root transitions
  z_(i,m) ↦ z_(i,m')^(m'/m). `activeColimit` is its chosen colimit, with actual
  coprojections. The category `Under B[1/f]` expresses compatible structural
  maps; this connected directed diagram has the same underlying ring colimit.
- `d : ℕ` permits d=0. `theta` is an isomorphism in `Under Q∞.right` from the
  canonical scalar extension of D to `Fin d → Q∞.right`, exactly θ∞ as a
  Q∞-algebra isomorphism. No degree invertibility or Galois action is assumed.

### Rendering of every conclusion

- The first conjunct asserts that every inactive parameter maps to a unit of A.
  Consequently puncturing at the full product agrees canonically with puncturing
  at the active product; the ring used in the statement always retains the full
  product, as the original definition Q_m=T_m[1/f] does.
- The existential index m is by construction positive and prime to p.
  `theta_m` is a Q_m-algebra isomorphism D⊗Q_m ≅ Q_m^d.
- For every original x∈D and coordinate j, the first displayed equation says
  ι_m(θ_m(x⊗1)_j)=θ∞(x⊗1)_j. This is exactly equality of the scalar extension
  with the given θ∞: algebra maps from D⊗Q∞ are determined by D and Q∞,
  and both maps fix Q∞. It does not assert only the existence of some splitting.
- `strictStage t m` is the canonical ring pushout of C_m←B→A, hence S_m
  with both structural maps. `strictPuncture` pushes out B[1/f]←B→S_m and
  is S_m[1/f]. `k` is a morphism over B[1/f] into this puncture. Its two
  equations fix every coefficient in A and send every active root to the
  matching full-root coordinate. Polynomial quotient and localization
  universal properties therefore specify the actual canonical map uniquely;
  this is not an unconstrained ring map in a hypothesis.
- `ambient t m D` is D_m=D⊗_(B[1/f]) C_m[1/f], retaining its C_m-structure.
  `strictAmbient` is its tensor extension along C_m→S_m. `Theta` is an
  isomorphism over S_m into S_m[1/f]^d. Its equation on D says it extends
  exactly theta_m through k. Together with S_m-linearity, this determines it
  on D, S_m and the inverted f, hence on the entire scalar extension.
- `IsIntegral S_m x ↔ ∃ a, localization(a)=x` states precisely that the integral
  closure of S_m in S_m[1/f] is its structural image, including rings with
  several components. No domain hypothesis is used for S_m or A.
- `closure (ambient t m D)` is Mathlib's actual `integralClosure C_m D_m`,
  with its actual subtype inclusion. `strictClosure` base-changes this very
  E_m along C_m→S_m; canonical tensor associativity identifies it with
  E_m⊗_B A, not a separately chosen extension of the punctured cover.
- `epsilon` is the resulting S_m-algebra isomorphism to S_m^d. The last map
  equality says its coordinatewise localization equals Theta composed with
  the base-changed actual inclusion of E_m. Thus this is a restriction of
  the same splitting, not an unrelated product isomorphism.
- Taking spectra of epsilon gives the asserted trivial finite etale cover:
  Spec of the finite product is d disjoint copies of Spec S_m, over Spec S_m
  by the identity on every copy. Under Spec, the pushout defining
  strictClosure is the actual base change of Spec E_m along Spec A→Spec B.
  This geometric consequence is rendered by its equivalent affine algebra
  isomorphism, including its structural map.

### Dependency declarations and representation choices

All helper maps are public declarations in the owning module, listed in
`lean.declarations`, each with the source and blueprint docstring. They just
assemble existing notions, so no new independent definition node is needed.

The original dependency declarations used are `IsNoetherianRing`
(`Mathlib.RingTheory.Noetherian.Defs`), `MvPolynomial`
(`Mathlib.Algebra.MvPolynomial.Basic`, underlying the existing root quotient),
`IsIntegrallyClosed`, `IsDomain`, `Localization.AtPrime`
(`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` and its imports),
`Localization.Away` (`Mathlib.RingTheory.Localization.Away.Basic`),
`integralClosure` and `IsIntegral`
(`Mathlib.RingTheory.IntegralClosure.Algebra.Basic`), and `colimit`, `colimit.ι`
(`Mathlib.CategoryTheory.Limits.HasLimits`). Finite etaleness is expressed
through `RingHom.Finite` and `RingHom.Etale`, equivalent to the recorded
finite-etale scheme definition on affine spectra. Tensor products are
expressed by Mathlib's canonical commutative-ring pushouts:
`CommRingCat.isPushout_tensorProduct` in
`Mathlib.Algebra.Category.Ring.Constructions` identifies them with
`TensorProduct` and fixes both pure-tensor inclusions.
`Under.pushout`, `Under.map`, `Under.forget`, and `commAlgCatEquivUnder`
provide the corresponding algebra interfaces without bespoke tensor instances.

The existing, landed definition nodes added to stmt_deps are:
`def-sfb-parameter-root-algebra` (`Algebra.pthRootAlgebra`,
`WeilConjectures.RingTheory.PthRootAlgebraLocal`),
`def-sfb-simultaneous-root-tower` (`Algebra.RootTowerIndex`,
`Algebra.simultaneousRootDiagram`, `Algebra.simultaneousRoot`, and
`Algebra.simultaneousRootTransition`, `Sheaf.RingTheory.SimultaneousRootTower`),
`def-weil-pbc-strict-henselization-limit`
(`Scheme.strictHenselizationScheme` and `Scheme.strictHenselizationRing`,
`WeilConjectures.AlgebraicGeometry.StrictHenselization`),
`def-weil-pbc-strict-henselization-structural-map`
(`Scheme.strictHenselizationStructuralMap`, corresponding upstream module),
and `def-weil-geometric-point` (`IsAlgClosed`, with `Scheme.SpecToEquivOfField`
explaining the point-and-residue-field interpretation). Their node files and
records are unchanged. The original `def-sc-ring-strict-henselization` module
`Sheaf.RingTheory.StrictHenselizationPresentationIn` is publicly imported;
the added geometric construction supplies the specific object required here.

Already stated proof inputs are imported: `RingHom.exists_map_of_finitePresentation_colimit`
from `Sheaf.RingTheory.ColimitCategoryFpAlgebras`,
`Scheme.strictHenselization_indEtale_of_affine_chart` from its upstream module,
`CommAlgCat.filteredColimit_tensorProduct_elementwise` from its upstream module,
`integral_totalFraction_mem_range_of_normal` from its upstream module, and
`TensorProduct.toIntegralClosure_bijective_of_indEtale` from
`Sheaf.RingTheory.IntegralClosureIndEtaleBaseChange`.
The imports also expose the recorded finite-presentation, etale base-change,
and ind-etale definitions. `lem-sfb-monic-quotient-faithful-tensor-coordinates`
has no Lean declaration recorded in the read repository, so there is no
module for that proof-only dependency to import yet. It is retained in the
DAG and in the proof docstring, with no duplicate declaration invented.

### Edge cases and statement check

Checked r=0, s=0, m=1, d=0, empty covers, zero B, non-domain normal C_m,
noninjective root-tower transition maps, and arbitrary degree d including
p dividing d. Empty products are Mathlib's empty finite products. Fin 0→R
is the zero ring and Spec of it is empty. The coefficient ring B=0 has no
geometric point, consistently with the original quantification. No proof
uses regularity of A, any Galois group or roots of unity. The active embedding
retains the original labels, and all root maps fix the A-coefficients.
There are no `let`/`show` statement binders, auto-bound variables, file-local
notations or local instances. A common arbitrary universe is used for the
rings and their geometric point, as in the existing strict-localization API;
root orders remain the actual small set of positive integers.
No STATEMENT-DISPUTED issue or node correction was found.

### Search record

- LeanFinder: “A specified splitting of a finite etale algebra over a root tower
  descends to a finite level and splits its normalization over a strict henselization”.
  Eight hits, including `Algebra.Etale.iff_exists_algEquiv_prod`,
  `Algebra.Etale.exists_subalgebra_fg`, and local etale quasi-finite lemmas;
  none states this specified-splitting descent and normalization result.
- Loogle: `MvPolynomial, AdjoinRoot, integralClosure, TensorProduct` returned
  zero hits.
- Mathlib grep: `(root|Kummer).*(strictHensel|integralClosure)|` followed by
  `(strictHensel|integralClosure).*(root|Kummer)` returned eight hits on
  cyclotomic integrality and general integral-closure results, no match.
- Project rg: `activeRoot|active_root|ActiveRoot|rootTower|RootTower|root tower|Kummer`
  and the item id in `lean/WeilConjectures` and `lean/Sheaf` found no existing
  statement. Refinement to root-algebra and root-diagram names found the
  landed `SimultaneousRootTower` and `Algebra.pthRootAlgebra`, both reused.
  The earlier strict-local Kummer theorem requires a regular local ring and
  a prime-to-p group torsor, so is not this statement.
- `tools/blueprint_refs.py search 'active root tower'` returned no blueprint nodes.
  DAG search found the already landed simultaneous-root diagram and parameter-root
  algebra nodes, so they are cited instead of adding duplicates.
- LeanSearch: the specified finite-etale root-tower descent and strict-local
  integral-closure query returned eight hits, including etale finite-data descent,
  field product decompositions and local etale criteria. No hit states the given
  splitting's finite-level descent together with its restriction to the actual
  normalization. The exact query and response summary are in searches.jsonl.

Validation uses only scompile.py, separately for this module; no global build
or live repository write is performed. The full nine-step proof is carried
in the theorem docstring for stage 3.

## Second reading by Q146

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
