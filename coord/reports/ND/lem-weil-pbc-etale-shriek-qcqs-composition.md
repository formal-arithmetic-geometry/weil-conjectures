## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition` states
`AlgebraicGeometry.Etale.nonempty_iso_etaleShriek_qcqs_compactification_comp`, with `sorry`.
It asserts existence of a natural isomorphism between the functors for three specified
compactifications. No definition, new node, dependency module, or statement correction is needed.

Hypotheses and clauses, in order:
- Finite commutative ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
- Schemes X, Y, Z: `{X Y Z : Scheme.{u}}`; qcqs for each is
  `[CompactSpace X] [QuasiSeparatedSpace X]` and the corresponding Y and Z instances.
- The composable morphisms are `(f : X ⟶ Y) (g : Y ⟶ Z)`.
- Separated finite type for each is `[IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]` and the corresponding g instances. Finite type means locally finite
  type and quasi-compact, with no finite-presentation or Noetherian hypothesis.
- The three choices are `(cf : Compactification f) (cg : Compactification g)
  (cgf : Compactification (f ≫ g))`. The structure contains the intermediate scheme,
  open immersion `i`, proper map `g`, and factorization `comm`. Its open immersion is
  quasi-compact because the original morphism is: see
  `Compactification.quasiCompact_openImmersion` / `quasiCompact_openImmersion_iff`.
  This also applies to the composite, which is quasi-compact.
- The definition `Rh_!^c = Rp_* j_!` is precisely the existing
  `rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c`:
  `D+(openImmersionLowerShriek _ c.i) ⋙ R+(lowerStar _ c.g)`.
- The bounded-below small-etale module categories are the domain and codomain of this
  existing functor: `DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat Λ))`.
- Existence of a natural isomorphism is `Nonempty (F ⋙ G ≅ H)`. Lean composes functors
  left to right, so `F ⋙ G` is the paper's `Rg_! Rf_!`. The assertion is about entire
  functors on D-plus, rather than separate objectwise isomorphisms. No coherence clause
  is added.

Dependency declarations inspected and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- The conventions node fixes no declaration: its Mathlib properties are used as above.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` and its documented
  bounded-below counterpart `rightDerivedLowerShriekOfCompactificationPlus`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`, used inside that functor.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `AlgebraicGeometry.Etale.lowerStar`;
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`, used by the same definition.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded six-functor encoding with
  `DerivedCategoryModule`, `DerivedCategory.Plus`, and `ModuleCat.{u+1} Λ`.
- Proof-only import `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
  supplies the recorded direct-image composition statement. The recorded extension-by-zero
  adjunction and exactness modules are already publicly imported by LowerShriek. The
  compatible-triangle, open-proper-interchange, and compactification-independence nodes
  have no Lean record at the time of writing, so no import is available for those nodes.

Source read: `literature/stacks-project/more-etale.tex`, label
`lemma-shriek-composition` (0F7J), including the compatible triangle and four-line
calculation. The module docstring includes all five DAG proof steps, ending in comparison
with the arbitrary supplied choices (0F7I).

Edge cases checked: empty schemes and empty open immersions are allowed by the structures;
zero coefficient ring is allowed by CommRing and Finite; identity and proper morphisms
admit their identity compactifications. There is no nonempty, nonzero, characteristic,
invertibility, smoothness, Noetherian, or finite-presentation assumption. Coefficients
live in the established `u+1` universe, so the usual finite rings are available by lifting.
All objects and universe variables are explicitly bound. There are no disputed statements.

Searches for an existing declaration:
- msearch.py leanfinder: "Composition of compactification based derived lower shriek
  functors on bounded below small etale sheaves". Eight generic sheaf/Kan-extension hits,
  including `RanIsSheafOfIsCocontinuous.fac` and `sheafPushforwardCocontinuous`; no match.
- msearch.py loogle: "rightDerivedLowerShriekOfCompactificationPlus,
  rightDerivedLowerShriekPlusCompIso". Zero hits, unknown identifier for the project name.
- msearch.py grep: "shriek|Shriek" in Mathlib AlgebraicGeometry. Zero hits.
- rg in upstream `WeilConjectures/SixFunctors/Etale` for shriek and Compactification:
  inspected `LowerShriek.lean`, `LowerShriekComposition.lean`, and Compactification/Defs.
  The unbounded compatible-model composition and the bounded-below chosen-model
  composition exist, but neither directly states this theorem for three supplied choices.
  The latter is `rightDerivedLowerShriekPlusCompIso` with HasCompactification choices;
  the former is `rightDerivedLowerShriekOfCompactificationCompIso`, unbounded and restricted
  to compatible models. Therefore neither is recorded as an exact existing statement.
- rg in upstream for this node id: no hit.
- rg in `lean/Sheaf` for shriek composition: hits include coherent
  `ProperUpperShriekComposition`, which is a different functor/category; no exact match.
- rg of the proposed declaration name in Mathlib, upstream, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no collision.

Validation: server-only scompile.py and deliver2.py --no-push; results recorded below.

## Second reading by ND

I read the node, its six statement dependencies and their recorded declarations,
all five proof steps, and `more-etale.tex`, the section
`section-derived-lower-shriek-compactification` and labels
`lemma-shriek-well-defined` (0F7I) and `lemma-shriek-composition` (0F7J).
The source works with a ring and torsion cohomology on D-plus, or a torsion
ring on the unbounded category. Every module over a finite ring is torsion,
so its bounded-below specialization is exactly the node's scope. The source
adds no Noetherian or invertibility assumption.

Independent object/hypothesis/conclusion checklist (all verdicts: match):

- Coefficients: finite commutative ring Lambda is `(Λ : Type (u + 1))
  [CommRing Λ] [Finite Λ]`. This includes the zero ring.
- Schemes: X, Y, Z are `{X Y Z : Scheme.{u}}`, the recorded Mathlib scheme
  and morphism category of def-pc-scheme, not schemes over an extra base.
- Qcqs for each scheme is `[CompactSpace X] [QuasiSeparatedSpace X]`,
  likewise Y and Z. These are the underlying topological qcqs properties.
- Two composable morphisms are `(f : X ⟶ Y) (g : Y ⟶ Z)`.
- Separated finite type is `[IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]`, likewise g, following the scheme-conventions node.
  No finite-presentation hypothesis is substituted for finite type.
- Three arbitrary choices are `(cf : Compactification f)
  (cg : Compactification g) (cgf : Compactification (f ≫ g))`.
  I read Compactification/Defs: its fields Z, i, g, comm, isProper and
  isOpenImmersion are exactly the factorization data required here.
  Although this structure alone permits a non-quasi-compact open, its
  `quasiCompact_openImmersion_iff` proves the required condition for each
  choice, since f, g and their composite are quasi-compact. Thus no extra
  compactifications enter this quantification.
- Model functor: I read both variants in Derived/LowerShriek. The recorded
  unbounded `rightDerivedLowerShriekOfCompactification` has the documented
  bounded-below counterpart used here,
  `rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c`.
  Its body is exactly the derived degreewise extension by zero followed
  by bounded-below right derived lowerStar. No new definition is needed.
- Underlying operations: I opened `openImmersionLowerShriek` in its recorded
  OpenImmersion/Defs module and `lowerStar` in UpperLowerStar/Defs, and
  `rightDerivedLowerStarPlus` in Derived/UpperLowerStarCoherence. They use
  the small etale sites, not the big etale or pro-etale topology.
- Categories: the source and target of the model functor are
  `DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat Λ))`.
  I read the recorded DerivedCategories module, which explicitly adopts
  this six-functor encoding of constant-coefficient module sheaves.
- Conclusion: `Nonempty (F_cf ⋙ F_cg ≅ F_cgf)` is an isomorphism of whole
  functors, natural in the D-plus input. Functor composition in Lean gives
  the node's Rg_! after Rf_!. Each compactification is universally bound
  before existence of the isomorphism. The node asks for no coherence,
  and the statement adds none.

Edge cases: empty schemes and empty open immersions are permitted; there
is no Nonempty binder. The zero complex and zero coefficient ring are
included. Identity and proper morphisms retain the stated scope (the
existing `Compactification.ofIsProper` includes their identity opens).
There is no degree n, index family or excluded characteristic. A single
scheme universe and coefficient/module universe u+1 follow the recorded
DerivedCategories convention; universe lifting accommodates every finite
coefficient ring. All variables and universes are explicitly bound.

Independent searches, using different wording from the author:

- msearch leanfinder: "Natural isomorphism between compactly supported
  etale direct images for arbitrary compactifications of two composable
  scheme morphisms". Eight hits, chiefly Scheme.Modules.restrictFunctorComp
  and scheme open-immersion identities: none is the requested theorem.
- msearch loogle: `"lowerShriek", "comp"`: zero hits.
- rg of Mathlib AlgebraicGeometry for `shriek|properSupport|compactlySupported`:
  no hits. rg of the upstream derived etale files and project Sheaf files
  for compactification/composition and nonempty shriek isomorphisms found
  the upstream LowerShriekComposition module; I opened its declarations.
  Its OfCompactificationCompIso is unbounded and uses compatible choices;
  PlusCompIso uses chosen HasCompactification instances rather than the
  three supplied choices. Its hom_eq theorem requires a compatible triangle.
  None is an exact existing signature for this node. Other project hits
  concern geometric towers or different functors, not this assertion.
- rg of the proposed declaration in the upstream declaration index found
  no collision. The original worker's three search kinds are also retained.

H12/H13: no new nodes or dependency modules are delivered. All required
notions already have usable public declarations, including the bounded-below
counterpart of the compactification model. The direct-image composition
proof dependency is imported without public and I opened its signature.
The other unstated proof dependencies have no module to import. The
statement docstring faithfully records the node's five proof steps, with
source tags and blueprint id. There is one theorem with exactly `by sorry`,
no data definition, private notation, local instance or hidden let binder.
The node's lean.statement matches the file signature verbatim.

Mismatches and repairs: none. The Lean module and node are retained unchanged;
this independent review and its validation are appended to the report.
