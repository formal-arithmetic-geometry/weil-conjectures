## Worker report

The module `Sheaf.Paper.IntegralTwistBaseChange` states
`WeilConjectures.integral_twist_base_change`, with one `sorry` and the complete eight-step
DAG proof in its docstring. It reuses the actual published scalar isomorphisms, rather
than asserting an unspecified family of isomorphic objects. No node statement or dependency
list was changed. There are no new DAG nodes or dependency repairs.

The auxiliary declarations merely expose the arrows occurring in the scheme-naturality
clause of this item: `integralTwistAbSheaf` forgets the existing module action;
`IntegralTwistSchemeArrows` contains a completed coefficient sheaf map, root-limit map,
and signed-line maps to direct images. `IsCanonicalIntegralTwistSchemeArrows` specifies
these maps by finite coefficient projections, finite root projections, semilinearity,
unit, root-tensor, positive tensor-power and negative evaluation equations.
`IntegralTwistSchemeArrows.AreIsomorphisms` states invertibility of their inverse-image
adjuncts. These are only transparent interfaces for this theorem's canonical naturality
arrows, not alternative constructions of any coefficient object or Tate twist. There
is no choice of new data from a mere existence result. The theorem asserts existence
and uniqueness of normalized scheme arrows, so naturality is not conditional on arbitrary
unsupplied maps. All auxiliary declarations have this item's blueprint tag and source.

Hypotheses and clauses, in order:

- Prime ell is `(l : ℕ) [Fact l.Prime]`. The scheme is `S : Scheme.{u}` with
  `[∀ x : S, Invertible (l : S.residueField x)]`. There is no finite-field datum,
  characteristic restriction beyond invertibility, nonemptiness, or geometric finiteness
  hypothesis.
- The finite extensions are `E F : Type u`, each with `Field`, `Algebra ℚ_[l]` and
  `FiniteDimensional ℚ_[l]`. Their inclusion is the specified `ι : E →ₐ[ℚ_[l]] F`.
  Field homomorphisms are injective; the statement includes identity embeddings and does
  not choose an algebraic closure or an integral basis.
- `R_H` is precisely `completedIntegralCommRingSheafUnrestricted l H S`, the recorded
  inverse limit of constant residue-ring sheaves, with unchanged multiplication. The
  coefficient inclusion is `integralCompletedScalarMap`, characterized by all finite
  quotients. No discrete coefficient ring is substituted for this completion.
- `T` is `purTwistZlModule S l`, whose underlying abelian sheaf is the actual root-tower
  limit `purTwistZlOne`. The first integral line is the recorded
  `purTwistIntegralModule S l H`: its original underlying constant-scalar tensor is
  equipped with the completed action via clause 3 of `pur_twist_sheaf_locally_free`.
  No extra identification is assumed as a hypothesis.
- For every signed integer, `integralTwistLine l H S m` is the recorded
  `coefficientTwistLine`: unit at zero, `coefficientTwistPower` at positive exponents,
  and `SheafOfModules.homObj` into the unit at negative exponents. Thus every negative
  case is the sheaf dual, not module Hom of global sections.
- The actual isomorphism is `twistLineScalarIso l E S F ι m`, of type
  `(integralOrdinaryScalar l E F ι S).obj (integralTwistLine l E S m) ≅
  integralTwistLine l F S m`. The published ordinary scalar functor is precisely
  sheafified change of rings, with target coefficient as first factor. Symmetry
  identifies this with the node's notation having the target coefficient last.
  The second conjunct specifies its hom on EVERY local pure tensor as
  `b tensor x ↦ b • twistScalarMaps(x)`. This determines the isomorphism as a
  sheaf map and is stronger than a bare `Nonempty` iso assertion only in spelling
  out the canonical map already required by the node.
- The first conjunct, `IsCanonicalTwistScalarMaps ... (twistScalarMaps ...)`, explicitly
  asserts all four defining equations. Its zero clause is the coefficient inclusion;
  its first-line clause preserves root tensors; its positive recursion commutes with
  `siteSheafTensorTmul`; its negative clause sends evaluation on the positive line
  to the coefficient image of evaluation. Together with the scalar-iso formula these
  are exactly tensor-associativity for nonnegative powers and the evaluation-induced
  dual base-change map for negative powers. The recursion includes every tensor power;
  dual evaluation gives the contractions between opposite powers as well. All equations
  are imposed on every object U, hence also after every further localization.
- Tower compatibility is the third conjunct, for every finite extension G and embedding
  `κ : F →ₐ[ℚ_[l]] G`, every m, U and local section x. It equates the direct
  semilinear comparison for `κ.comp ι` with the composite comparisons. By the second
  conjunct, on an iterated scalar tensor this equates the two isomorphisms under the
  usual scalar associator: both take `(c tensor b) tensor x` to
  `c * κ(b) • c_EG(x)`. This retains arbitrary scalar sections and all signs.
- Scheme naturality is the final universally quantified clause, for every
  `X : Scheme.{u}` on which ell is invertible and every `h : X ⟶ S`. This is the
  category of schemes on which the twists in the statement are considered; in fact
  invertibility on X follows from invertibility on S and existence of h, so making
  its typeclass explicit excludes no morphism in the source. The theorem supplies
  unique normalized comparison arrows aE and aF, proves their inverse-image adjuncts
  are isomorphisms, states the completed-ring inclusion square, and states the signed
  line inclusion square on every U and section. The coefficient square and these
  semilinear squares, together with the pure-scalar-tensor formula, are precisely
  naturality of the displayed scalar-extension isomorphisms. Direct-image squares
  are equivalent to the inverse-image squares under `proEtaleSheafAdjunction`.

The site has object universe u+1 and morphism universe u throughout; sheaf sections are
in u+1. No equality between those two site universes is imposed. A common ambient u
contains the schemes and finite coefficient fields, following the recorded twist API.

Dependency declarations read and used:

- `def-weil-completed-integral-coefficients`: import
  `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its public coefficient
  modules. Uses `completedIntegralCommRingSheafUnrestricted`,
  `completedIntegralCommRingProjectionUnrestricted`, `integralCoefficientCommRingSheaf`.
- `def-coefficient-twists-detailed`: `Sheaf.Paper.CoefficientTwistsDetailed`;
  uses `coefficientTwistLine`, `coefficientTwistPower`, `integralTwistLine`,
  `IsCanonicalTwistScalarMaps`, `twistScalarMaps`, `twistLineScalarIso`.
  Read the actual root/tensor/evaluation normalizations and scalar-iso signature.
- `lem-pur-twist-sheaf-locally-free`: `Sheaf.Paper.PurTwistSheafLocallyFree`,
  publicly imported by the twist module; `purTwistZlOne`, `purTwistZlModule`,
  `purTwistIntegralTensor`, `purTwistIntegralModule` and the full four-clause theorem.
- `def-pur-sheaf-hom`: upstream
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `SheafOfModules.homObj`; the signatures, section interpretation and docstrings
  were read. The negative-exponent evaluation uses its localized-site functional.
- `def-pur-sheaf-tensor-product`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`,
  `siteSheafTensorTmul` and the reexported `siteSheafTensorRight` and independent-universe
  change-of-rings constructions. No tensor notion was copied.
- `def-weil-pbc-proetale-site`: Mathlib
  `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt`, `ProEt.topology`.
- Stated proof dependencies are imported without `public`:
  `Sheaf.CategoryTheory.ModulePullbackTensorIso` (`module_pullback_tensor_iso`),
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed` (`tensorClosed`),
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback`
  (`finite_free_dual_pullback`).
- `def-weil-proetale-inverse-image`: `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  publicly imported by `ProEtaleRootsOfUnityInverseImage`; uses `proEtaleBaseChange`,
  `proEtaleSheafDirectImage`, and `proEtaleSheafAdjunction`.
  The latter module also supplies the canonical finite root direct-image map.
- `lem-pur-integral-twist-line-inverse-image` has no recorded Lean module to import.
  It is a proof dependency, not an assumed theorem in this statement. The present
  naturality clause spells out and asserts the necessary canonical arrows with their
  projection/tensor/evaluation normalizations directly, including their existence,
  uniqueness and invertibility, rather than leaving missing construction data as
  an extra hypothesis or waiting on that node. No separate theorem claiming to
  formalize all of that independent node is introduced.

Edge cases checked before writing: m=0 is multiplication/unit scalar extension;
m=1 preserves the actual root tensor, m=-1 evaluates against that root tensor; every
negative exponent is covered by `Int.negSucc`. E=F and identity inclusions give the
unit comparison by normalization; the tower includes identities. Empty S has trivial
sheaves, and all normalization, uniqueness and isomorphism clauses still hold.
Ramified coefficient extensions are allowed; nothing asserts unramifiedness or that
an integral basis is canonical. No nonempty-cover or positive-rank condition on the
scheme is imposed. Scheme naturality includes arbitrary maps and the empty source.

Searches made (all through the prescribed search wrapper or read-only rg):

- LeanFinder: "Completed integral Tate twist lines commute with finite scalar extension
  naturally in the scheme and compatibly with tensor powers duals and towers".
  Eight results: scheme pullback tensor congruences and adic-completion tensor naturality;
  no completed Tate-line comparison with all required clauses.
- Loogle: `Module.Dual.baseChange, TensorProduct.assoc`: zero hits.
- Mathlib grep: `baseChange.*[Dd]ual|[Dd]ual.*baseChange|tateTwist`:
  nine hits in algebraic dual base change, transvections and the Picard group, no
  completed sheaf Tate-line statement.
- LeanSearch: "Completed integral Tate twist sheaves commute with scalar extension and
  pullback naturally, for tensor powers and duals": eight results including
  `IsBaseChange.toDualBaseChange`, `TensorPower.pairingDual`, and module-sheaf pullback
  APIs. These are ingredients, not this completed coefficient statement.
- Read-only rg in Mathlib, upstream WeilConjectures and lean/Sheaf for
  `IntegralTwistSchemeArrows|integral_twist_base_change|IsCanonicalIntegralTwistScheme`:
  no existing declarations with these names.
- Upstream rg for this item id and `IsCanonicalTwistScalarMaps|coefficientTwistPower|
  twistScalarMaps`: no hits. Project rg found the canonical scalar arrows and towers
  in `CoefficientTwistsDetailed`, reused here, but no theorem including scheme
  naturality. The source blueprint's integral/common-stage sentence and current
  main-20261015 proof were read alongside the full DAG proof.

No STATEMENT-DISPUTED flag or mathematical node fault was found. The first compilation
identified a typeclass action hidden by direct-image notation and the explicit
invertibility instance needed to use the signed comparison at X. The former is exposed
by typed `@id`, and the latter by quantification over schemes on which ell is invertible;
neither changes the mathematical statement. Final validation uses only scompile.py and
the delivery wrapper's per-file compilation and preflight.

## Second reading by Q123

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
