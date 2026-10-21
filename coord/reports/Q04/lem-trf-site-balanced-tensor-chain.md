## Worker report

The delivery states `SheafOfModules.BalancedTensorChain.existsUnique_balancedTensorChain`
in `Sheaf.Algebra.Homology.BalancedTensorChain`, with its sole proof `sorry`.
The five helper definitions have real terms: `source`, `target`, `sourceSection`,
`targetSection`, and `Normalized`. They name the composites and local generator formulas
of this comparison, using the existing module categories, scalar extension, tensor,
sheafification, and totalization. No separate mathematical notion or dependency repair
is needed, and the node changes only in `lean`.

Hypothesis and clause correspondence:

- A site small in the module universe is `{C : Type u} [Category.{v} C]`
  with `[EssentiallySmall.{r} C]` and `{J : GrothendieckTopology C}`.
  Site objects and arrows keep independent universes `u` and `v`; no equality with
  the coefficient/module universe `r` is imposed. The imported coefficient-universe
  instances supply the sheafification and local-equivalence structures.
- The commutative ring sheaves and their morphism are
  `{R S : Sheaf J CommRingCat.{r}}` and `(φ : R ⟶ S)`.
  `J.HasSheafCompose (forget₂ CommRingCat RingCat)` records the existing forgetful
  passage from commutative ring sheaves to the ring sheaves used by module sheaves.
- Module sheaves are the recorded `CategoryTheory.ringedSiteModules` abbreviation
  of `SheafOfModules`. Restriction is exactly `SheafOfModules.restrictScalars`
  along the image of `φ` under that forgetful sheaf functor.
- Scalar extension is represented by a functor `E` with `[E.Additive]`,
  `hobj : ∀ M, E.obj M = changeOfRings φ M`, and `hmap`, which identifies every
  `E.map f` with `changeOfRingsHom φ M f`, with only equality transports.
  These specify the canonical sheafified tensor construction on objects AND maps;
  they introduce no flatness condition or arbitrary comparison map. This is the
  same ordinary-functor interface already used by
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients` and by the consumer
  `CategoryTheory.siteDerivedTensorRestriction`. Additivity is a property of
  that specified extension functor, not an extra condition on φ or the modules.
- Every possibly unbounded P is quantified as a `CochainComplex ... ℤ`, with no
  support/boundedness predicate. N is an arbitrary S-module sheaf. Its `N[0]` is
  `(HomologicalComplex.single _ (.up ℤ) 0).obj N`. Termwise restriction and
  extension are the corresponding `mapHomologicalComplex (.up ℤ)` functors.
  In particular extension has terms `E.obj (P.X i)` and differential `E.map (P.d i j)`,
  fixed by `hobj` and `hmap` to the stated tensor terms and differentials.
- `source φ P N` is `HomologicalComplex.tensorObj P (U.mapHomologicalComplex.obj N[0])`.
  This writes restriction of N[0] directly; it is canonically the same degree-zero
  complex as UN[0], including its zero components. `target φ E P N` is termwise
  restriction of `HomologicalComplex.tensorObj (E.mapHomologicalComplex.obj P) N[0]`.
  `tensorObj` is Mathlib's `mapBifunctor` for the recorded monoidal sheaf tensor:
  its coproduct total has second differential `(-1)^p (1 tensor d)`.
- The existential family `a` consists of chain isomorphisms from this `source`
  to this `target`, in the category of R-module sheaf complexes. Inverse identities
  and commutation with every differential are part of this isomorphism type.
- `sourceSection` takes x and n to the presheaf pure tensor, then the module
  sheafification unit, then `tensorObjIsoSheafification.inv`, then the actual
  `HomologicalComplex.ιTensorObj` inclusion in bidegree `(i,0)`.
  `singleObjXSelf.inv`, restricted through U, places n in degree zero.
- `targetSection` first forms `s tensor x` in the existing scalar-extension
  presheaf and applies its sheafification unit and `hobj` transport. It then
  applies the outer sheaf-tensor unit and total summand inclusion with n.
  The scalar-first order `s tensor x` is the project's existing representation
  of the statement's `x tensor s` under the usual tensor symmetry.
- `Normalized` is precisely the two equations
  `a.hom (sourceSection x n) = targetSection x 1 n` and
  `a.inv (targetSection x s n) = sourceSection x (s • n)`, for every integer i,
  site object V, and all original x,s,n sections. No assertion that arbitrary
  tensor sheaf sections are tensor products of sections occurs anywhere.
- The next conjunct quantifies an arbitrary chain isomorphism b and asserts
  `Normalized ... b → b = a P N`. Thus normalization alone characterizes each
  comparison, without requiring naturality as part of the uniqueness hypothesis.
- Simultaneous naturality quantifies arbitrary chain maps f and S-module maps g.
  Its square uses `HomologicalComplex.tensorHom f (U_complex.map (single.map g))`
  on the source and restriction of `tensorHom (E_complex.map f) (single.map g)`
  on the target. Both are composed with the SAME existential family a.
- Homotopy compatibility quantifies arbitrary `h : Homotopy f f'` and arbitrary g.
  It compares every `(i,j)` component of the actual
  `HomologicalComplex.mapBifunctorMapHomotopy₁`, with its target version obtained
  by `E.mapHomotopy` and `U.mapHomotopy`, against `a.hom.f j` and `a.hom.f i`.
  In particular `(i,i-1)` is the requested degree-minus-one intertwining square.
  These are actual homotopies of the tensor maps, so the same natural family
  passes to chain maps modulo homotopy, not merely to cohomology.
- The last conjunct gives an S-module sheaf H in each degree, an R-linear
  isomorphism c identifying its restriction with the source degree, and an
  S-linear isomorphism d with the target degree before restriction. The equation
  `c.hom ≫ a.hom.f (i+0) = U.map d.hom` says that both directions of a are
  sheaf morphisms for the lifted action. The explicit local equation
  `c.hom (s • c.inv (sourceSection x n)) = sourceSection x (s • n)` fixes that
  action to act through N. Since H is an actual S-module SHEAF, its actions
  commute with restrictions, rather than being unrelated sectionwise modules.
- There is no flatness, K-flatness, derived category, projective resolution,
  boundedness, or Tor-amplitude assumption in the theorem.

Dependency declarations used, with the recorded interfaces read in full:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, its preadditive and localization
  instances and coefficient-universe sheafification instances. This imports
  the recorded tensor/scalar-extension construction.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`:
  `SheafOfModules.changeOfRings`, `changeOfRingsPresheaf`, `changeOfRingsHom`;
  `...Sheaf.Monoidal`: `tensorObjIsoSheafification`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` and its additive instance.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafificationAdjunction` and its unit.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  `...Bifunctor`: `HomologicalComplex.mapBifunctor`, `ιMapBifunctor`;
  `...Monoidal`: `HomologicalComplex.tensorObj`, `tensorHom`, `ιTensorObj`;
  `...BifunctorHomotopy`: `HomologicalComplex.mapBifunctorMapHomotopy₁`;
  `...Homotopy`: `CategoryTheory.Functor.mapHomotopy`;
  `...Single`: `HomologicalComplex.single`, `singleObjXSelf`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: recorded abstract complex/
  derived-category interface; only cochain complexes are needed here.
- Proof imports follow the DAG:
  `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`
  (`PresheafOfModules.existsUnique_bilinear_sheafification_extension`),
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
  (`SheafOfModules.tensor_bilinear_universal`), and Mathlib presheaf tensor.
  The proof docstring lists all seven node proof steps. No import of the
  downstream `Sheaf.Paper.SiteDerivedTensorRestriction` is introduced.

Edge cases checked mathematically before writing and on rereading:

- The zero complex or zero N: the actual total and unit generators vanish;
  the comparison is the unique zero-object isomorphism.
- The zero target ring and modules, and identity φ: all scalar-extension and
  action formulas still make sense; no nonzero-ring or proper-quotient assumption.
- Empty sites or covering families: use the existing sheaf/tensor construction,
  not pointwise-generation or existence-of-a-site-object hypotheses.
- P unbounded in both directions: the total is still the coproduct total;
  N[0] has just one possibly nonzero row, so there is no product total or
  convergence assumption hidden in the statement.
- Arbitrary positive, zero, and negative i: indices are all integers, and the
  explicit `(i,0)` inclusion lands in `i+0` without a chosen degree bound.
- Homotopies with nonzero degree-minus-one components and maps g changing N:
  the comparison uses the genuine induced homotopies and arbitrary g, so this
  clause is stronger than a bare chain-map naturality equation in the required way.
- Different site object/morphism sizes are retained in every helper and in E.

Searches for an existing complete statement (2026-10-21):

- `msearch.py ... leanfinder "balanced tensor change of rings isomorphism for sheaves
  of modules natural in cochain complexes"`: eight hits on pullback/free-module
  formulas and presheaf tensor restrictions; no balanced normalized chain family.
- `msearch.py ... loogle "SheafOfModules.restrictScalars, TensorProduct.assoc"`:
  zero hits.
- `msearch.py ... grep "balanced|tensor.*[Cc]hange|[Cc]hange.*[Tt]ensor"
  Algebra/Category/ModuleCat`: nine hits, including algebraic tensor base change;
  none states the sheaf chain and homotopy comparison.
- `msearch.py ... leansearch "sheaf module tensor scalar extension balanced chain
  isomorphism"`: eight hits, notably algebraic `cancelBaseChange` and
  `distribBaseChange`; these do not include sheafification, totalization, or
  the chain/homotopy normalization.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `balancedTensor|balanced_tensor` found existing ordinary balanced contractions
  and isomorphism criteria and the downstream derived restriction theorem.
  Reading them showed they concern other tensor orders, ordinary modules, or
  derived/K-flat consumers; none states this unrestricted chain family.
- `rg` of both source roots and `dag/lean_names_upstream.json` for
  `balancedTensorChain|existsUnique_balancedTensorChain|BalancedTensorChain`
  found no declaration collision.

Source checked directly in `literature/stacks-project/sites-modules.tex`,
Section `section-tensor-product`: the sectionwise tensor, sheafification, tensor
identities and bilinear universal property. The node's seven-step construction
fixes the balanced chain/homotopy normalization and is reproduced in the docstring.
No statement dispute or correction.

## Second reading by Q04

A separate reading pass compared the node's full statement with every definition and
conjunct. The first draft's family uniqueness required all compatibility clauses;
this was tightened to the explicit componentwise assertion that the two generator
formulas alone determine b. The first compile also found that scalar `1` and a
restricted module's underlying S-module needed explicit type indications; the
canonical scalar action is now applied to `@id (H.val.obj V) (...)`.

The source/target helpers are the same actual total tensors, not arbitrary models.
Both original local formulas include each sheafification unit; n enters the degree-zero
complex through `singleObjXSelf.inv`, and the extension factor order matches the existing
construction. The naturality and homotopy clauses use the same a, arbitrary f and g,
and the actual tensor-induced homotopies. The action clause records an S-module sheaf,
S-linear comparison and the through-N scalar formula. All integers and unbounded P
remain quantified; there is no K-flat premise. No dependency node, source statement,
or proof step required changing. The main theorem is the only postponed proof.
