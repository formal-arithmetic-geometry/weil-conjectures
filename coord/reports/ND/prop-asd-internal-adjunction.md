## Worker report

This delivery attaches the existing canonical bifunctor isomorphism
`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIsoOfFinite` in
`WeilConjectures.SixFunctors.Etale.Derived.TensorHom`. No Lean module is written and
no theorem is proved. The published declaration and its complete docstring were read
using `scompile.py --source`; the older slopmaster2 checkout lacks this finite-specialized
definition, although it has the general canonical construction and the objectwise theorem.

Hypotheses and clauses:

- The coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` in the enclosing
  `TensorHom` section. The node's formerly unintroduced A is made explicit as below.
- Schemes are `{X Y : Scheme.{u}}`, the morphism is `(f : X ⟶ Y)`, and compactifiability
  is `[HasCompactification f]`, using the existing `Compactification` factorization.
  The existing construction applies in particular to Noetherian X and Y, as its docstring
  explicitly observes; no new hypotheses on the node's schemes are needed.
- Arbitrary M and K are the arguments of the bifunctors on
  `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))` and its Y analogue.
  No boundedness, constructibility, or Tor-amplitude condition appears.
- `RHom(X)[ModuleCat Λ]` is `Etale.derivedHom`, contravariant in M. Whiskering on the left
  with `R(f)^![ModuleCat Λ]` evaluates its second argument at f^times K. Whiskering on
  the right with `R((f)_*[ModuleCat Λ])` takes the ordinary unbounded derived direct image.
- The right bifunctor `(R(f)_![ModuleCat Λ]).op ⋙ RHom(Y)[ModuleCat Λ]` evaluates at
  `(op M,K)` to RHom(Rf_! M,K). The result is an isomorphism of bifunctors, hence natural
  in both complexes, with precisely the displayed direction.
- Canonicity is actual data: the definition specializes `derivedHomRightDerivedLowerShriekIso`
  using `isIso_projectionMap_of_finite`. That construction is `conjugateIso` of the
  projection formula through the ordinary, tensor-Hom, and exceptional adjunctions.
  Its component is the evaluation/counit transpose specified by the node's proof, not
  an unspecified inhabitant of Nonempty.
- Ordinary small-etale module coefficients are used throughout; nothing is transported
  to a pro-etale or completed coefficient category.

Dependencies read and used for identification:

- def-amb-etale-compact-support: `Etale.rightDerivedLowerShriekOfCompactification`,
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`; chosen `rightDerivedLowerShriek`
  is exactly this composite of derived extension by zero and proper derived direct image.
- def-asd-compactifiable: `AlgebraicGeometry.Compactification` and `HasCompactification`,
  `WeilConjectures.Compactification.Defs`, reexported by
  `Sheaf.AlgebraicGeometry.CompactifiableOverField`; its recorded theorem supplies the
  additional field-case existence clause, unnecessary for a morphism already compactifiable.
- def-weil-pbc-derived-categories: `Etale.DerivedCategoryModule`,
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, reexported by
  `Sheaf.AlgebraicGeometry.DerivedCategories`. These are exactly the categories here.
- def-pur-derived-internal-hom: `CategoryTheory.derivedInternalHom`,
  `Sheaf.Algebra.Homology.DerivedInternalHom`, is the general ringed-site encoding.
  The existing upstream exchange uses the equivalent constant-module coefficient interface
  `Etale.derivedHom` from `WeilConjectures.SixFunctors.Etale.Derived.Hom`: internal Hom
  right adjoint to the recorded derived tensor. No second definition is supplied.
- def-kun-derived-tensor: `Etale.derivedTensor`,
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor`, at ModuleCat Λ.
- thm-amb-etale-exceptional-adjoint: the recorded
  `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification` in
  `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint` has finite commutative coefficients.
  Upstream `Etale.rightDerivedUpperShriek` and `rightDerivedUpperShriekAdjunction` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` choose precisely a right adjoint
  of that compact-support functor for the chosen compactification.
- prop-weil-pbc-inverse-image-modules-exact:
  `AlgebraicGeometry.etaleInverseImageModulesExact`,
  `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`, identifies exact inverse image
  with module pullback. This is the adjunction used upstream in `UpperLowerStar`.
- lem-weil-pbc-kinjective-total-derived:
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective`,
  `Sheaf.CategoryTheory.KInjectiveTotalDerived`, supplies the unbounded interpretation.
  Upstream uses its existing total right-derived machinery, not a bounded-below replacement.

Edge cases: M and K may be zero or unbounded in both directions. Empty schemes and the
zero coefficient ring are not excluded. No invertibility of the coefficient order on the
schemes is imposed. The common coefficient universe u+1 is exactly the recorded ordinary
etale encoding; it does not equate unequal site object and morphism universes. An identity
morphism and open or proper morphisms are all covered by HasCompactification.

Searches (2026-10-15):

- msearch.py leanfinder, query `derived internal Hom exceptional inverse image compact
  supports internal adjunction`: eight unrelated LightCondensed, exponentiable-morphism,
  and locally-constant adjunction results; no Mathlib match.
- msearch.py loogle, query
  `AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedLowerShriek`: unknown
  identifier in the Mathlib index, zero results.
- msearch.py grep, query `internalHom|lowerShriek|exceptional`, subdirectory
  AlgebraicGeometry: zero results.
- rg in upstream WeilConjectures for `internalAdjunction|derivedHomRightDerivedLowerShriekIso`
  finds TensorHom's canonical generic construction and its finite objectwise specialization.
  rg for the node id there gives no result in the older checkout.
- rg in lean/Sheaf for those names and the node id finds only the explanatory proof
  citation in SmoothGenericDirectImage, not another declaration of this statement.
- The current published TensorHom source, requested through scompile.py --source,
  additionally has the exact finite bifunctor declaration bearing this node's blueprint id.
  This is why an existing record is used rather than duplicating it.

## Statement corrected

Old statement, verbatim:

For a compactifiable morphism $f:X\to S$ between
Noetherian schemes, and arbitrary complexes $M$ on
$X$ and $K$ on $S$, there is a canonical isomorphism

$$
Rf_*R\mathcal Hom_A(M,f^\times K)
\xrightarrow{\sim}R\mathcal Hom_A(Rf_!M,K).
$$

The notation refers to derived pullback and internal Hom, and ordinary etale compact supports.

The old text did not introduce A. The correction prepends only
`Let $A$ be a finite commutative ring.` This spells out the finite-level ordinary-etale
coefficient scope of the containing unit sk-prop-sf-cbc and the already corrected dependency
thm-amb-etale-exceptional-adjoint. The published TensorHom declaration for this exact
blueprint node confirms this scope explicitly. No change is made to complexes, morphisms,
conclusions, or the proof. This node is not the containing unit's own statement.

Every citer was found by rg over dag/nodes and then checked for actual stmt_deps/proof_deps
membership; all three uses survive:

- prop-coef-integral-dualizing: holds true; applies the internal adjunction at the finite
  levels A_n before passage to the derived limit, never directly at integral coefficients.
- lem-weil-delta-proper-pushforward: holds true; its statement already specifies finite
  coefficients invertible over the field.
- lem-asd-smooth-generic-direct-image: holds true; the argument uses the finite field F_ell.

No citer is edited. There are no new nodes or dependency modules.

## Second reading by ND

I independently read the corrected node, its six proof steps, the original blueprint
prop-asd-internal-adjunction and its containing sk-prop-sf-cbc section, and the current
published TensorHom module obtained again with scompile.py --source. I read the corrected
coefficient scope against these sources before comparing Lean. Verdict: keep the existing
record and correction; no mathematical or Lean-record repair is needed.

Object/hypothesis/conclusion checklist:

1. A finite commutative coefficient ring A: the enclosing TensorHom section binds
   `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`. This is a ring, not a field, and includes
   nonreduced rings and the zero ring. Verdict: matches the corrected coefficient scope.
   The unit explicitly distinguishes finite-stage ordinary-etale coefficients from integral
   pro-etale coefficients. The exceptional-adjoint dependency likewise explicitly assumes
   a finite commutative ring. Introducing A resolves the formerly unbound coefficient;
   it does not change the unit's statement or replace integral coefficients by discrete ones.
2. Schemes X and S and their morphism f: `{X Y : Scheme.{u}} (f : X ⟶ Y)`, with Y playing
   S. The node assumes Noetherian schemes. The existing construction applies to all schemes
   with the stated compactification; specialize to Noetherian X and Y as lean.note specifies.
   This reuse of a general existing interface adds no hypothesis or excluded case. It does
   not assert that the natural-language node itself proves the non-Noetherian extension.
3. A compactifiable f: `[HasCompactification f]`. I read Compactification.Defs: the data
   are Z, proper g : Z ⟶ Y, open i : X ⟶ Z, and `f = i ≫ g`; HasCompactification is
   existence of these data. This is precisely the defining clause of def-asd-compactifiable.
   Its field-specific existence theorem is not an additional assumption here. Verdict: match.
4. Arbitrary complexes M on X and K on S: the domain of the bifunctors is
   `(DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))ᵒᵖ`, with second
   argument in the corresponding Y category. Evaluation at `(op M, K)` binds the complexes
   after the ring, schemes, morphism, and compactification. No Dplus, bounded, constructible,
   perfect, or finite Tor condition occurs. Verdict: match, including quantifier order.
5. Ordinary etale categories: I read Coefficients.DerivedCategoryModule, which abbreviates
   exactly these unbounded ModuleCat-valued sheaf derived categories. I read the node and
   recorded interface of def-weil-pbc-derived-categories; this is its designated encoding.
   No pro-etale or derived-complete category is substituted. Verdict: match.
6. Source of the arrow: `RHom(X)[ModuleCat Λ]`, followed by whiskering left with
   `R(f)^![ModuleCat Λ]` and whiskering right with `R((f)_*[ModuleCat Λ])`, evaluates to
   `Rf_* RHom_X(M, Rf^! K)`. Hom.derivedHom is MonoidalClosed.internalHom, right adjoint
   to Tensor.derivedTensor; these definitions were opened. The general ringed-site
   derivedInternalHom dependency uses K-injective Hom complexes instead, on SheafOfModules;
   the existing constant-module encoding renders the same internal derived Hom, rather
   than a new private definition. Verdict: match.
7. Target of the arrow: `(R(f)_![ModuleCat Λ]).op ⋙ RHom(Y)[ModuleCat Λ]` evaluates to
   `RHom_Y(Rf_! M, K)`. I read LowerShriek.rightDerivedLowerShriekOfCompactification:
   its body is `D((c.i)_!open[A]) ⋙ R((c.g)_*[A])`; rightDerivedLowerShriek uses the chosen
   compactification. This is the functor recorded by def-amb-etale-compact-support.
   UpperShriek.rightDerivedUpperShriek is its chosen right adjoint, with
   rightDerivedUpperShriekAdjunction, and the finite coefficient left-adjoint instance
   supplies it without an additional hypothesis. Verdict: match.
8. Canonical isomorphism in the displayed direction, natural in both complexes:
   the actual data `derivedHomRightDerivedLowerShriekIsoOfFinite` have this bifunctor
   isomorphism type. Its body supplies isIso_projectionMap_of_finite and calls
   derivedHomRightDerivedLowerShriekIso. I read that construction: conjugateIso of the
   projection isomorphism through the parametrized tensor-Hom, ordinary inverse/direct
   image, and exceptional adjunctions. Its component is thus the evaluation/counit mate
   of the node, contravariant in M and covariant in K, rather than an arbitrary selected
   objectwise isomorphism. Verdict: match.

Dependency and proof checks: I opened all eight statement-dependency records and their
relevant source declarations, including EtaleExceptionalAdjoint's explicit compactification
and Noetherian binders, EtaleInverseImageModulesExact's constant-ring and module-adjunction
interface, and exists_rightDerived_of_enough_isKInjective's universal property and
K-injective computation clause. None supplies an extra assumption in the specialized
existing declaration. I also read Stacks sites-cohomology.tex lemma-adjoint (07A6),
lemma-internal-hom (08J9), and sites-modules.tex lemma-j-shriek-and-tensor (0E8I) and
lemma-j-shriek-reflects-exactness (0E8G). These are for arbitrary ringed sites/topoi and
unbounded derived objects, so they add no coefficient invertibility or boundedness condition.
The six node proof steps respectively give the ordinary derived adjunction, tensor-Hom
adjunction, open projection formula, compactified projection formula, natural Hom-bijection
chain, and its evaluation/counit transpose. The upstream generic construction and its
finite specialization implement precisely that chain. Existing-source docstrings identify
the blueprint and construction; no new statement, proof, or definition is delivered, so
there is no new sorry or hollow data and no new module needing H8/H9 repair.

Correction/citer audit: an independent scan of stmt_deps and proof_deps found exactly the
three citers listed in statement_change. I opened all three source texts. In
prop-coef-integral-dualizing the invocation is explicitly at A_n before derived limits;
in lem-weil-delta-proper-pushforward it is for finite coefficients invertible over a field;
in lem-asd-smooth-generic-direct-image it is for F_ell. All three holds:true verdicts
survive, including the requirement to use the specified evaluation mate. None is edited.

Edge cases: empty schemes and identity/open/proper compactifications are admitted. M or K
may be zero and unbounded in both directions. No index or degree n is bound, so no empty
index or n=0 exception is introduced. There is no restriction on scheme characteristic or
invertibility of the coefficient order. The coefficient universe u+1 and Scheme.{u} are
the project's ordinary-etale convention, with arbitrary u; all variables are bound by
explicit source section declarations. No equality of site object/morphism universes is
imposed. Finiteness does not require nontrivial coefficients.

Independent searches used different queries from the first worker:

- LeanFinder: `right adjoint compact support pushforward derived sheaf Hom tensor mate`;
  eight ordinary module/sheaf adjunction hits, none the desired exchange.
- Loogle: `"conjugateIso"`; ten general mate-equivalence hits, not an etale compact-support
  theorem. This confirms the categorical tool, not a replacement for the statement.
- LeanSearch: `derived direct image internal Hom exceptional inverse image is internal Hom
  of compact support direct image`; service returned Internal Server Error, recorded as
  unavailable; no negative mathematical conclusion is inferred from this failure.
- Mathlib grep through msearch: `TensorHom|derivedHom|lowerShriek` in AlgebraicGeometry;
  only three unrelated Over.tensorHom occurrences.
- Direct rg over all upstream WeilConjectures, Mathlib, and project lean/Sheaf for
  `derivedHomRightDerivedLowerShriek|internalAdjunction|internal.adjunction`: upstream
  TensorHom contains the generic construction and objectwise specialization. The project
  also has internalHomCounitMate_isIso; I opened it: it concerns a tensor-preserving left
  adjoint and its counit, not Rf_! with exceptional adjoint and Rf_* on these categories.
  SmoothGenericDirectImage only cites this node in its proof docstring.
- Fresh scompile.py --source TensorHom confirms the exact published finite bifunctor
  specialization and its surrounding binders. Its recorded lean.statement is verbatim
  its signature before `:=`; retaining existing:true avoids duplicating it.

Mismatches/changes: no defect found in the node copy or existing Lean record. Appended
this independent audit only. There are no new definition nodes or dependency modules.
Validation uses deliver2.py's scompile-backed existing-declaration probe and server preflight;
there are no delivered Lean files to compile separately.
