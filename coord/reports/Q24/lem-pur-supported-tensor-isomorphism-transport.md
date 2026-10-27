## Worker report

This is the stage-2 Lean attachment for lem-pur-supported-tensor-isomorphism-transport.
The Q82 PASS on 2026-10-22 is a stage-1 split review: its report explicitly says no
Lean was written or compiled, and the live node has no lean record. I preserve its
statement, seven proof steps, dependencies, source and all maintained metadata.
There is no maintenance repair note for this item. This delivery does not resplit it.

Module: Sheaf.Paper.SupportedTensorIsomorphismTransport. Main declaration:
WeilConjectures.FiniteOpenProduct.supportedTensorIsomorphismTransport.
All six helpers are in WeilConjectures.FiniteOpenProduct.SupportedTensor and are
listed in lean.declarations. They name composites and predicates belonging to the
item, as authorized by the missing-helper rule, not independent notions or copies
of the dependency operations. Every definition has real data. The main theorem is
the only sorry and carries the complete seven-step natural-language proof.

Hypothesis-by-hypothesis rendering:

- The finite datum k,A=A_(E,n) is S : PurityFiniteSetting.{u}, with
  S.Coefficient the recorded ULift of S.Ring, the actual positive-level quotient.
  The already published FiniteOpenProduct.settingCoefficientFinite instance supplies
  finiteness from Padic.finite_coefficientExtensionRing, with no new hypothesis.
- W,Y,W',Y' are Scheme.{u}. Each has its structure over Spec S.field.k;
  IsSeparated on the structure morphism renders separated over k, and
  LocallyOfFiniteType together with QuasiCompact renders finite type over k.
  All four are bound explicitly. No compatibility with their structure morphisms
  is imposed on i,i',g,h: the node specifies scheme maps and scheme isomorphisms.
- i : W ⟶ Y, i' : W' ⟶ Y' have the two IsOpenImmersion instances.
  g : Y ≅ Y', h : W ≅ W' are actual scheme isomorphisms.
  s : IsPullback h.hom i i' g.hom renders the Cartesian square, and s.w.symm
  is precisely i ≫ g.hom = h.hom ≫ i' for the canonical square comparison.
- R',H' are arbitrary FiniteD S.Coefficient Y'; P',Q' are arbitrary
  FiniteD S.Coefficient W'. FiniteD is the existing ordinary unbounded derived
  category of pro-etale sheaves with fixed module scalars. There is no bounded,
  constructible, perfect, finite-Tor, or individual-support restriction.
- a',b' are exactly the two displayed isomorphisms from pullback along i'.
  f' is an isomorphism from the tensor of R',H' to extension of the tensor P',Q'.
  hf' is SupportedTensor.UnitEquation at i' on f'.hom, namely
  pull(i').map f' = mu_i'.hom ≫ tensorMap a'.hom b'.hom ≫ eta'.
  This retains the actual section-normalized adjunction unit.

Definition and conclusion clause-by-clause rendering:

- R,H,P,Q are written out as the four pull.obj expressions, so the statement has
  no let binders or hidden choices. SupportedTensor.identification is square.app
  followed by pull(h).mapIso a' (respectively b'), exactly the specified a,b.
- SupportedTensor.transport is mu_g.inv, pull(g).map f'.hom, beta.app at P' tensor
  Q', then finiteShriek(i).map mu_h.hom. Composition is Lean's left-to-right ≫.
  This is exactly the node's f, using its recorded normalized beta.
- The first conjunct is IsIso of this very morphism, rather than existence of
  some unrelated isomorphism. The second is its UnitEquation with the transported
  identifications, hence the precise displayed equation for Li* f.
- The third and fourth conjuncts quantify over every D0 in FiniteD on W and assert
  Function.Injective of pull(i).map on precisely the two Hom sets from R tensor H
  and H tensor R to finiteShriek(i).obj D0. No general ambient faithfulness is used.
- The fifth conjunct explicitly states the in-particular uniqueness of f among
  morphisms with the same source, target and restriction.
- SupportedTensor.reverse is sigma(H,R) ≫ f ≫ finiteShriek(i).map sigma(P,Q),
  using the recorded derived Koszul symmetry, with both swaps retained.
  The sixth conjunct is its reversed UnitEquation; the seventh says every map
  satisfying that equation equals this very signed conjugate.
- The eighth conjunct is IdentityEquation at i' and the given primed inputs.
  It specializes transport to (Iso.refl Y', Iso.refl W', IsPullback.of_id_fst).
  The equality is transport(f') ≫ i'_!(tensorMap idUnit_P' idUnit_Q') =
  tensorMap idUnit_R' idUnit_H' ≫ f'.hom. Thus both arrows are compared after
  the actual identity-pullback unitors on all four inputs, with no arbitrary lift
  or equality of differently presented derived objects. identityPull is the
  degreewise localization of ProEtale.upperStarId followed by
  Functor.mapDerivedCategoryIdIso. The identity square is not silently excluded.

Dependency declarations read and used:

- Sheaf.Paper.PurityFiniteSetting: WeilConjectures.PurityFiniteSetting,
  PurityFiniteSetting.Ring, PurityFiniteSetting.Coefficient, their ring structures.
- Sheaf.Paper.FiniteOpenProductSwap (recorded module for
  def-sf-finite-open-tensor-operations): WeilConjectures.FiniteOpenProduct.tensor,
  tensorMap, tensorIsoMap, pull, tensorPullIso, adj, pullComp, pullCongr, square,
  beta, sigma, proetSigma and settingCoefficientFinite. Their full constructions
  were read. No private operation copy is introduced.
- Sheaf.SixFunctors.OpenTensorNormalization:
  SheafOfModules.OpenTensorNormalization.finite_compatibility,
  exists_normalized and SheafOfModules.openTensorNormalization. The first has the
  actual finite A specialization and its comparison equalities. FiniteD and
  finiteShriek are its public imported definitions from OpenTensorNormalizationData.
- Sheaf.Paper.DerivedPullbackTensorIso:
  WeilConjectures.derivedPullbackTensorIso and its canonical finite composition,
  associativity, unit and signed-braiding clauses. This is a proof-only import.
  The fixed-scalar operations in the statement are exactly those required by the
  definition dependency; there is no restriction to higher-coefficient subcategories.
- identityPull uses the exact existing
  AlgebraicGeometry.ProEtale.upperStarId from
  WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs.

The operations' existing owner module also contains the downstream
finiteOpenProductSwap theorem. This statement must import that module to use its
recorded operations. Adding an import of the present module back to that parent
would close an import cycle; its proof-dependency import must therefore be omitted
under stages/2-statements.md section 3(7). No operation is duplicated to hide this.

Sources read: the item's full node and each dependency's statement/Lean record;
all recorded operation signatures and docstrings; the full finite normalization
signature; the derived pullback/tensor theorem's finite and higher clauses and
proof plan; blueprint main-20261015 sec-six-functors/sk-thm-sf-kunneth-relative/
lem-sf-kunneth-coherence.proof.md, especially its final symmetry reduction.
The item's transport result is expressly agent-formulated, not falsely attributed
to a literal Stacks theorem. Its retained seven-step proof is used verbatim in intent.

Edge cases checked: empty W (the assumed supported isomorphism makes the tensor
source zero); zero tensor inputs; i or i' the identity; the identity Cartesian
square, explicitly stated with its unitors; odd shifts (both Koszul symmetries
are retained, so cancelling signs is legitimate); genuinely unbounded objects;
arbitrary D0; neither tensor factor separately supported. The site retains
object universe u+1 and morphism universe u and coefficients Type (u+1).
Universes and variables are all explicitly bound with autoImplicit false.
No disputed statement or source correction was required.

Searches for existing statements (all run for Q24 and this item on 2026-10-22):

- msearch leanfinder: "Canonical transport of a supported tensor isomorphism along
  a Cartesian square of scheme isomorphisms, uniqueness after open restriction
  and signed conjugation". Eight hits on Scheme.Pullback.Triplet.tensorCongr
  and related carrier-ring transports; none concerns unbounded pro-etale module
  categories, normalized extension by zero or this theorem.
- msearch loogle: "CategoryTheory.Adjunction.homEquiv, Function.Injective".
  Successful query, zero hits; no exact attachment.
- msearch grep: "extensionByZero|openImmersion.*Faithful", CategoryTheory.
  Successful query, zero hits.
- msearch leansearch: "Open restriction is injective on maps from a tensor product
  isomorphic to extension by zero and preserves a normalized comparison under
  Cartesian isomorphism transport". Eight ordinary scheme/ringed-space
  IsOpenImmersion restriction results, none states this derived theorem.
- rg of Mathlib, lean/WeilConjectures and lean/Sheaf for
  supportedTensorIsomorphismTransport, namespace SupportedTensor, def UnitEquation,
  def IdentityEquation: no hits. Exact grep of the item id in lean/WeilConjectures:
  no hits. Searches for supported/tensor/transport terminology in the source
  pro-etale modules and FiniteOpenProductSwap found no exact statement. Broader
  searches found supported quasi-coherent and ordinary module comparison modules,
  whose coefficient categories and assertions differ. The existing swap theorem
  depends on the present item and is not an attachment for it.

Validation: scompile.py compiled the statement module separately both as a sandbox
and with its library module name; no errors or unexpected warnings. The sole
postponed theorem is the node itself, with its complete proof docstring. Delivery
preflight and final compile are run by deliver2.py.

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
