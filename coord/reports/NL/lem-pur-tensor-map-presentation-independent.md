## Worker report

The module `Sheaf.Paper.TensorMapPresentationIndependent` states
`AlgebraicGeometry.ProEtale.tensorMap_presentation_independent`, with one `sorry` and
no other postponed proof. Its thirteen helper definitions construct the canonical
arrows occurring in this statement. They belong to this node's single tensor-map
notion and are listed in `lean.declarations`. No dependency record, natural-language
statement, or DAG edge was changed. No new node or dependency module was needed.

### Matching the hypotheses and objects

* The primes p and ell, their inequality, positive finite-field exponent, algebraic
  closure k, finite subextension E of the fixed ell-adic algebraic closure, valuation
  ring, specified uniformizer, and positive coefficient level n are the existing
  `P : WeilConjectures.PurityFiniteSetting.{u}`. The coefficient ring throughout is
  `P.Coefficient`, the recorded `ULift` of the actual quotient O_E/(varpi_E^n).
  The existing `finiteComparedCoefficientFinite` supplies finiteness. In particular
  there is no extra ramification-index divisibility hypothesis.
* `X Y : Scheme.{u}` and their `Over (Spec (.of P.field.k))` structures give the
  schemes over k. The two `LocallyOfFiniteType` and `QuasiCompact` pairs on their
  structure maps say finite type; the two `IsSeparated` instances say separated.
* `f : X ⟶ Y`, `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, and
  `QuasiCompact f` give precisely the separated finite-type k-morphism.
  `d : ℕ` and `SmoothOfRelativeDimension d f` say smooth of pure relative dimension
  d >= 0, using the dependency's existing Mathlib class. No positive-dimension
  assumption, surjectivity, or nonempty-fibre assumption is added.
* The categories are ordinary module sheaves on `Y.smallEtaleTopology` and
  `Scheme.ProEt.topology Y`, with values `ModuleCat.{u + 1} P.Coefficient`, and their
  existing derived categories. This preserves the small-site universe convention:
  schemes in u, site objects and module values in u+1. No equality of site object
  and morphism universes is imposed.
* The theorem uses the recorded cohomological-smoothness dependency's etale-origin
  coordinates: `K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology ...)` and `_hK`
  assert that its comparison pullback is in
  `ProEtale.DerivedCategory.constructibleFiniteTor`. These coordinates test every
  pro-etale Dctf object: bounded constructibility supplies a bounded-below etale
  antecedent with a specified isomorphism, and no special representative is fixed.
  This is the same domain used by `finiteComparedTensorClause`. The geometric
  input K of the node is thus nu_Y^* K in the displayed Lean coordinate system.
* The existing `Etale.upperStar ... f |>.leftDerivedFunctor` is Lf* in etale
  coordinates. Its comparison with pro-etale pullback identifies its nu_X^* image
  with the node's M. `tensorPresentationEtaleRight A c` is the actual ordinary
  right adjoint at c, using the published finite-coefficient left-adjoint theorem.
  Its value at the coefficient unit represents omega_c. The comparison unit at
  that unit identifies it with `sfFiniteExceptionalAt A c` of the pro-etale unit.
  No arbitrary functor, projection, comparison, or map is an input.
* `c c' : Compactification f` are completely arbitrary compactifications, with
  the recorded open immersion, proper map and factorization, without a density
  condition. `tensorPresentationRightIso` is `rightAdjointUniq` after transport
  of the second ordinary adjunction through the existing canonical compact-support
  isomorphism `Etale.rightDerivedLowerShriekOfCompactificationIso`. Applying
  comparison pullback gives the node's b in these coordinates.
* `tensorPresentationSource` is Lf* K tensor omega_c, in that order, using the
  existing `Etale.derivedTensor`. The canonical monoidal and pullback comparisons
  identify its nu_X^* image with the actual pro-etale tensor source.
  The conclusion supplies `∃ hH : ∀ c, ...plus (tensorPresentationSource ...)`:
  boundedness of this source is a conclusion/domain obligation, not an extra
  hypothesis or an assumed etale witness. A canonical witness exists for this
  image by the identity comparison, so quantification over witnesses is nonvacuous.
* `tensorPresentationCounitArrow` is exactly compact support of symmetry, inverse
  projection, counit at the coefficient unit tensor identity, and left unitor.
  Its projection inverse uses the existing finite ordinary-etale projection
  theorem explicitly. No inversion of a pro-etale projection off the bounded
  finite-Tor domain is asserted.
* `tensorPresentationRealization` feeds comparison pullback of that arrow,
  preceded by `fixedCompactSupportComparisonIso`, into
  `specifiedExceptionalHomEquiv A c ... W ...`. Thus the chosen W really occurs
  in the constructed Hom chain. `tensorPresentationTargetIso` is comparison
  pullback of the ordinary right adjoint applied to the inverse of the actual
  derived comparison unit at K. This identifies the resulting target
  nu_X^* G_c Rnu_Y,* nu_Y^* K with nu_X^* G_c K. This is the target's canonical
  identification, not an arbitrary isomorphism. Transporting the entire composite
  through the canonical monoidal, unit, pullback, and compact-support comparisons
  is the node's pro-etale counit transpose. The construction uses the bounded
  comparison-class bijection, never a pro-etale ambient adjunction.
* `purityTensorPresentationRealization` specializes this construction to P and
  derives target compactness from `QuasiCompact` of its structure morphism. It
  introduces no `CompactSpace` hypothesis into the theorem.

### Matching every conclusion

1. The first conjunct quantifies over both c and c' and independently over every
   `Scheme.FixedEtaleOriginWitness` W and W' of their tensor sources. It states
   realization_c followed by nu_X^*(b_K) equals nu_X^*(1_M tensor b_unit) followed
   by realization_c'. `tensorPresentationSourceIso` is exactly the tensor functor
   on the canonical right comparison at the unit. Hence this is
   b_K o theta_c = theta_c' o (1_M tensor b_A), with every identification retained.
2. The second conjunct fixes c and quantifies over W and W', equating the two
   actual realized arrows. Combined with the first conjunct, this covers changing
   either witness at either of the two compactifications. Their antecedents and
   isomorphisms can be arbitrary, including automorphisms of an antecedent.
3. The third conjunct gives `Iso.refl` for both the right comparison and the
   induced tensor-source comparison at c=c. Witness changes fix the arrow by
   the second conjunct, so they have the identity normalization too.
4. The fourth conjunct quantifies over every c1,c2,c3 and gives the cocycle for
   the actual right and tensor-source comparisons. Pasting the first conjunct
   therefore gives the cocycle for identified tensor maps, including simultaneous
   witness changes, which already act as equality on each realized arrow.
5. The final conjunct ranges over every `hc : HasCompactification f` and c,W,
   so in particular covers the fixed constructible choice of the recorded
   cohomological-smoothness definition. It compares the realized map with
   `tensorPresentationSpecifiedMap` through `tensorPresentationSpecifiedIso` and
   tensor of its component at the coefficient unit. The specified map is literally
   comparison pullback of symmetry followed by `Etale.dualizingComplexTensorMap`,
   exactly the map used in `finiteComparedTensorClause`, with its source reordered
   as in the node. Quantifying over hc here is not an extra existence hypothesis:
   it accommodates the existing compactification already bound in each clause;
   the finite-type purity setting also provides one by Nagata.

The additional boundedness conclusion hH only supplies the domain of the Hom
bijections that the node already uses. It does not add a mathematical assertion
beyond their stated applicability. The theorem never asserts existence of an
adjunction on arbitrary unbounded pro-etale objects.

### Dependencies read and used

* `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`,
  `WeilConjectures.PurityFiniteSetting`, its quotient `Ring` and size-lift
  `Coefficient`. Read the structure and those definitions and their docstrings.
* `def-pur-co-smoothness`: `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`,
  `AlgebraicGeometry.ProEtale.IsCohomologicallySmoothFiniteCompared`,
  `finiteComparedTensorClause`, `finiteComparedDualizing`, and the existing
  `finiteComparedCoefficientFinite`. The final map is the same
  `Etale.dualizingComplexTensorMap` used by that dependency. No private copy of
  cohomological smoothness or of its tensor map is defined.
* `thm-sf-ambient-adjoint-class`:
  `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`,
  `AlgebraicGeometry.ProEtale.specifiedExceptionalHomEquiv`, including its full
  normalized Hom-chain definition and the bounded-target obligation.
  Its public dependencies provide the existing `sfFiniteExceptionalAt`,
  `Scheme.FixedEtaleOriginWitness`, `fixedCompactSupportComparisonIso`, and the
  original comparison-class structure with naturality and coherence fields.
* `def-weil-compactifications-refinements`:
  `WeilConjectures.Compactification.RefinementCategory`,
  `AlgebraicGeometry.Compactification.Refinement` and `category` (read their
  data and automatic properness). The theorem uses `Compactification f` and the
  existing canonical comparison constructed through common refinements.
* `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.SmoothOfRelativeDimension`. Read its affine-local
  standard-smooth signature and the smoothness consequence. Relative dimension
  is not replaced by a dimension of the total space.

Every recorded proof-dependency module is also imported (non-public when used
only for the later proof): `PullbackTorAmplitude`, `SfPreservationClass`,
`FiniteCoefficientTensorCtf`, `ProEtaleConstructibleOrigin`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`CompactSupportProjectionFormula`, `FixProjectionCompactificationComparison`,
`RingedDerivedTensorNative`, and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution`.
The complete six-step natural-language proof is in the theorem's docstring.

### Searches and edge cases

Searches were run with the prescribed msearch wrapper:

* LeanFinder: "Canonical compactification comparison preserves the exceptional
  tensor counit transpose independently of etale origin witnesses". Eight hits
  concerned Kaehler differentials, coalgebra counits, and Gamma-Spec; no match.
* Loogle: `CategoryTheory.Adjunction.homEquiv_naturality_left,
  CategoryTheory.Adjunction.homEquiv_naturality_right`. Zero hits for that combined
  query. The generic naturality laws do not state the geometric assertion.
* LeanSearch: "Canonical right adjoint comparison preserves tensor counit transpose
  under change of compactification". Eight hits included the useful generic
  `rightAdjointUniq_hom_app_counit`, monads and monoidal adjunctions; no theorem
  states this finite-coefficient geometric assertion with its retained witnesses.
* Mathlib grep: `compactification.*(tensor|counit)|tensor.*presentation`.
  Twenty-three hits were module presentations and representation/coalgebra tensor
  constructions, not this statement.
* Project searches in both `lean/WeilConjectures` and `lean/Sheaf` used
  `tensor.*(Presentation|presentation)|Tensor.*(Presentation|presentation)|theta.*[Ii]ndep|tensor.*[Ww]itness`.
  Read the relevant canonical exceptional maps, comparison monoidal maps,
  specified class Hom chain, and compact-product retained-witness constructions.
  None states this tensor-map presentation-independence result. A direct search
  for the node id in both trees returned no declaration.
* Full-name searches for `tensorMap_presentation_independent` and the new
  `tensorPresentation...` names in Mathlib, both project trees and
  `dag/lean_names_upstream.json` found no full-name collision. Other namespaces'
  private module-presentation helpers are unrelated.

Before writing, checked the zero complex, empty X and Y, dimension d=0, n=1,
identical compactifications, non-dense compactifications, all three compactifications
identical, and arbitrary witness automorphisms. There is no Nonempty scheme,
positive d, ramification-index divisibility, proper f, invertibility of omega,
or cohomological-smoothness assumption. Identity and cocycle clauses retain the
canonical comparisons even for these cases. `autoImplicit false` is set, both
universes are explicit, every declaration has a source/blueprint docstring,
every line is at most 100 characters, and all data definitions have real bodies.

Validation: scompile.py compiled the helper constructions and then the complete
module with its theorem and all proof-dependency imports. The instance-resolution
failure in the first draft of the inverse projection was repaired by passing the
existing invertibility proof explicitly. Final validation and delivery use the
prescribed server preflight and per-file compile wrappers. There is no
STATEMENT-DISPUTED issue or source correction.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
