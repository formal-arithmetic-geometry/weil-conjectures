## Worker report

The module `Sheaf.AlgebraicGeometry.UnrestrictedFrobeniusFactorization` states the complete
node in three named theorems in `WeilConjectures.FiniteFieldDatum`. Each proof is `sorry`;
no definition, axiom, helper notion, new node, dependency repair, or statement correction
is introduced. All three declarations have source and step-by-step proof docstrings.

Sources read: main-20261015
`sec-smooth-purity/sk-def-sf-weil-complexes/def-pur-scheme-geometric-frobenius.md`,
the absolute-Frobenius display and second commuting square; Stacks `varieties.tex`,
`definition-absolute-frobenius` (03SM) and `lemma-frobenius-endomorphism-identity` (0CC7).
The node's fibre-product argument uses the recorded pullback universal property (01JP).
No repair note exists for this item.

Hypotheses and objects, used identically in all three declarations:

- `(D : WeilConjectures.FiniteFieldDatum.{u})` supplies p prime, a >= 1, q = p^a,
  the field k₀ of cardinality q, and its fixed arbitrary algebraic closure k with
  its structure embedding. These are the fields `prime`, `exponent_pos`,
  `cardinality_eq`, `card_base`, and the field/algebra/closure instances.
- `(T₀ : Over (Spec (CommRingCat.of D.k₀)))` is an arbitrary scheme over k₀;
  there are no finite-type, quasi-compactness, separation, smoothness, or
  nonemptiness binders. In the naturality theorem, `X₀ Y₀` are arbitrary such
  objects and `(f₀ : X₀ ⟶ Y₀)` is exactly a morphism over k₀.
- In the following correspondence only, write b for
  `Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))`. The actual signatures
  write this expression out; no file-local notation or let binder is used.
- T is `pullback T₀.hom b`; pi and rho are `pullback.fst T₀.hom b` and
  `pullback.snd T₀.hom b`, using the chosen pullback of the recorded dependency.
- F₀ is `T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a`.
  F is the same construction on T, with characteristic inherited along
  `pullback.fst T₀.hom b ≫ T₀.hom`. Thus the exponent is precisely q = p^a,
  and characteristic is obtained from the structure map rather than assumed.
- Phi is `((Over.pullback b).map (Over.homMk F₀
  (D.model_frobenius_over T₀.hom))).left`, with F₀ expanded in the signatures.
  This is the existing base-change functor applied to the actual model Frobenius.
- Sigma is `@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _
  (Fintype.ofFinite D.k₀) D.k _ _ _`; its underlying function is raising to
  `Fintype.card D.k₀ = D.q`. Gamma is its `.symm`. The canonical enumeration
  is supplied as a term, so no extra Fintype hypothesis is imposed.
- The two g maps are the recorded unrestricted `D.galoisMap T₀.hom` applied
  to sigma and its inverse. They are actual scheme maps induced by Spec of the
  field automorphism, not arbitrary maps and not required to be k-linear.
- The base-changed f is `((Over.pullback b).map f₀).left`.

Every conclusion clause (Lean's `≫` composes left to right):

| Node clause | Lean rendering |
| --- | --- |
| F₀ is over k₀ | First conjunct of `unrestricted_frobenius_projections`: `F₀ ≫ T₀.hom = T₀.hom`; also the exact proof supplied to `Over.homMk`. |
| pi F = F₀ pi | Second conjunct: `F ≫ pi = pi ≫ F₀`. |
| rho F = Spec(sigma) rho | Third conjunct: `F ≫ rho = rho ≫ Spec.map (CommRingCat.ofHom sigma.toRingHom)`. |
| pi Phi = F₀ pi | Fourth conjunct: `Phi ≫ pi = pi ≫ F₀`. |
| rho Phi = rho | Fifth conjunct: `Phi ≫ rho = rho`. |
| pi g_sigma = pi | Sixth conjunct: `g_sigma ≫ pi = pi`. |
| rho g_sigma = Spec(sigma) rho | Seventh conjunct: `g_sigma ≫ rho = rho ≫ Spec.map (CommRingCat.ofHom sigma.toRingHom)`. |
| F = g_sigma Phi | First conjunct of `unrestricted_frobenius_factorization`: `F = Phi ≫ g_sigma`. |
| F = Phi g_sigma | Second conjunct: `F = g_sigma ≫ Phi`. |
| Phi = g_gamma F | Third conjunct: `Phi = F ≫ g_gamma`. |
| Phi = F g_gamma | Fourth conjunct: `Phi = g_gamma ≫ F`. |
| g_sigma g_gamma = id | Fifth conjunct: `g_gamma ≫ g_sigma = 𝟙 T`. |
| g_gamma g_sigma = id | Sixth conjunct: `g_sigma ≫ g_gamma = 𝟙 T`. |
| f Phi_X = Phi_Y f | First conjunct of `unrestricted_frobenius_naturality`: `Phi_X ≫ f = f ≫ Phi_Y`. |
| f F_X = F_Y f | Second conjunct: `F_X ≫ f = f ≫ F_Y`. |

Dependency declarations inspected and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, with the
  complete structure and instances read. Its finite-type `geometricFiber` is
  deliberately not applied to unrestricted models.
- `Mathlib.AlgebraicGeometry.Over`: `AlgebraicGeometry.Scheme.Over`, `Hom.IsOver`,
  and the bundled `CategoryTheory.Over` convention. Morphisms in Over carry exactly
  the required structure-map equality.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the module docstring
  and `baseChange_morphism_projections` identify `Over.pullback` and its map with
  scheme/morphism base change. We use that functor directly.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift` and the universal property.
- `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`:
  `AlgebraicGeometry.Scheme.iterateFrobenius`, `iterateFrobenius_app_apply` and
  `natCast_eq_zero_of_natCast_top_eq_zero`; these allow zero rings and empty schemes.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.galoisMap`,
  `specGaloisMap_over`, `galoisMap_inverse`, and `galoisMap_projections`, whose
  full signatures have no finiteness assumptions. Its public dependency
  `Sheaf.AlgebraicGeometry.RelativeFrobeniusGeometricFiber` supplies the unrestricted
  `model_characteristic` and `model_frobenius_over`, used directly in the signatures.
  The finite-type `relativeFrobenius` and `geometricFrobenius` are not used.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Mathlib.FieldTheory.Finite.Basic`: `FiniteField.frobeniusAlgEquivOfAlgebraic`
  and its underlying q-power formula; proof dependencies `FiniteField.pow_card`
  and `pow_card_pow` are available from the same directly imported module.
- Proof-only recorded interfaces are imported from
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace` (ringed-space morphisms) and
  `Sheaf.AlgebraicGeometry.SchemeCharacteristic` (`Scheme.IsCharacteristic`).

Edge cases checked mathematically before writing:

- Empty T₀: the inherited characteristic proof concerns p = 0, not `CharP` of
  the zero ring; all endomorphisms and projection equalities exist. No nonempty
  or nontrivial hypothesis was introduced.
- T₀ = Spec k₀: the model Frobenius and Phi are identities; F equals the
  arithmetic coefficient action. This also checks that gamma, not sigma, cancels F.
- The nonreduced model Spec(k₀[e]/e²): Phi can kill nilpotents and is not claimed
  invertible; only coefficient maps have the two inverse identities.
- Infinite-type and nonseparated models: all terms use arbitrary schemes,
  actual base change and pullback universal properties; no finiteness instance
  is requested by the Lean signatures.
- a = 1 is included; a = 0 is excluded precisely by the input datum, as in the node.
- Identity and arbitrary model morphisms: both naturality equations have the
  correctly matched sources/targets. Absolute and coefficient Frobenii are
  scheme morphisms, so semilinearity imposes no mistaken k-morphism hypothesis.

Searches actually run, using `msearch.py Q89 lem-pur-unrestricted-frobenius-factorization`:

- LeanFinder: `Absolute Frobenius of a scheme over a finite field after scalar
  extension factors as model Frobenius and arithmetic coefficient Frobenius`.
  Eight hits included `IsPurelyInseparable.iterateFrobeniusₛₗ`,
  `WittVector.StandardOneDimIsocrystal.frobenius_apply`, `frobeniusEquiv_apply`,
  `FiniteField.frobeniusAlgEquiv`, `coe_frobeniusEquiv`,
  `RingHom.frobenius_comm`, `RingHom.map_frobenius`, and
  `WittVector.frobenius_eq_map_frobenius`; none states this scheme result.
- Loogle: `"frobenius", "comp"`. Hits included the inverse-composition lemmas
  for ring Frobenius equivalences, categorical Frobenius comparison, and coalgebra
  Frobenius identities; no scheme result.
- Mathlib grep: `frobenius|Frobenius` in `AlgebraicGeometry`: zero hits.
- LeanSearch: `Absolute Frobenius on scalar extension of a scheme over a finite
  field is the composite of model Frobenius and arithmetic coefficient Frobenius`.
  Eight hits were field Frobenius, LinearMap.frobenius, ring frobenius, and the
  `FiniteField.frobeniusAlgHom` / `frobeniusAlgEquivOfAlgebraic` formulas; no match.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for Frobenius factorization,
  projection, unrestrictedness and naturality located the dependency modules,
  `Sheaf.AlgebraicGeometry.FrobeniusFactorization`, and
  `Sheaf.SixFunctors.SchemeGeometricFrobenius`. The former assumes the model
  finite type; the latter has a purity/coefficient datum and only three of the
  six factorization/inverse conclusions. Neither states the present entire node.
  No import from the downstream purity module is used.
- Direct rg of `dag/lean_names_upstream.json` for `frobenius|Frobenius` and grep
  for this node id in `lean/WeilConjectures` found no exact existing attachment.
  Name-clash search for `unrestricted_frobenius_` in Mathlib and both project trees
  returned no hits before writing.

Validation: `scompile.py` compiled both the sandbox view and actual library module
on the server, cleanly (11.3 s and 9.3 s). The initial failed attempt was an explicit
argument-order error in Mathlib's arithmetic field-Frobenius declaration; it was
repaired by reading the declaration's variable order. No node fault or disputed
mathematical statement was found. The only JSON change is the item's `lean` record.

## Second reading by Q89

This is the worker's own second pass with the node and final file open; the dispatcher
brief forbids starting another agent and assigns independent review to the maintainer.
It is not claimed as an independent review. I checked that the first theorem contains
one over-base equality and all six displayed projection equations, that the second
contains all six factorization/cancellation/inverse equalities, and that the third
quantifies over every model morphism and contains both naturality equations. Reversing
right-to-left paper composition gives exactly the `≫` orders in the table above.
The Spec k₀ test distinguishes sigma from gamma; both inverse orders were checked.
No finite-type or separation assumption leaked through the formerly restricted
geometric-fibre interfaces. The datum and every universe/variable are explicitly bound;
there are no let binders, local notation, local instances, or data chosen from existence.
The only change following this pass was the field-Frobenius argument order already
reported above, after which both server compiler views passed.
