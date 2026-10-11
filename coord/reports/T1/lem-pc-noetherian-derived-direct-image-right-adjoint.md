## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint` states
`AlgebraicGeometry.noetherian_schemeDerivedDirectImage_has_rightAdjoint`, with exactly one
`sorry` proof and no new definitions. Its docstring carries all six proof steps of the node.

Hypotheses and clauses:

- Schemes X and Y are `{X Y : Scheme.{u}}`, and their morphism is `(f : X ⟶ Y)`.
- Noetherian X means `[IsLocallyNoetherian X] [CompactSpace X]`; Noetherian Y means
  `[IsLocallyNoetherian Y] [CompactSpace Y]`, exactly the node's stated definition.
- `HasDerivedCategory.{wX}` and `HasDerivedCategory.{wY}` on the shared sheaf-of-modules
  carriers supply the localization models used by the recorded definitions. These are
  structural model choices, not finiteness, boundedness or geometric hypotheses.
- The given derived direct image is the recorded `schemeDerivedDirectImage f`.
- Preservation of D_QCoh is the existential proof `h : ∀ E : schemeDerivedQCohCategory X,
  schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj)`. Quantifying over
  the full subcategory is equivalent to quantifying over every derived object together
  with its proof of quasi-coherent cohomology: its objects are precisely those pairs.
- The restricted functor is `(schemeDerivedQCohProperty Y).lift
  ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) h`.
  Mathlib's `ObjectProperty.lift` retains the same objects and maps and merely packages
  the target property. No arbitrary substitute functor or privately copied notion occurs.
- `.IsLeftAdjoint` on this restricted functor means it has a right adjoint:
  Mathlib's class has field `∃ right, Nonempty (left ⊣ right)`. The existential `h`
  expresses the first conclusion and allows stating the second dependent conclusion;
  it is not an assumed preservation hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` on the underlying scheme space.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory` (read their full definitions).
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage` (read its full definition and docstring).
- Mathlib's `CategoryTheory.ObjectProperty.lift`, `.ι` and
  `CategoryTheory.Functor.IsLeftAdjoint` supply restriction and adjoint-existence notation.

The imports use the direct-image dependency, the Noetherian predicate and adjoint-existence
class; the other recorded modules are available transitively. All variables and universes
are explicitly bound. Different derived-category hom universes wX and wY are allowed.

Edge cases checked before writing: empty source or target schemes are permitted (no
nonemptiness, point, field or dimension hypothesis); the zero complex and arbitrary
unbounded complexes are included; preservation requires every integer cohomological
degree through the existing QCoh predicate, including degree zero and negative degrees.
Identity morphisms and arbitrary nonseparated Noetherian schemes are included: only
quasi-separatedness, derived in the proof, is needed. No properness or finite-type
condition on f is imposed. There is no indexed-family universe restriction in this
statement. The four geometric assumptions are substantive, not universally inhabited.

Searches made (2026-10-11):

- `msearch.py ... leansearch "derived pushforward on quasi-coherent complexes of
  Noetherian schemes admits a right adjoint"`: UNAVAILABLE, Internal Server Error.
- `msearch.py ... leanfinder "derived direct image between Noetherian schemes preserves
  quasi-coherent cohomology and has a right adjoint"`: eight hits, all underived
  pushforward/pullback adjunctions (including Scheme.Modules.instIsRightAdjointPushforward)
  or generic site adjunctions; no match for a right adjoint of restricted derived direct image.
- `msearch.py ... loogle "CategoryTheory.Functor.IsLeftAdjoint,
  CategoryTheory.ObjectProperty.lift"`: zero hits. Direct source inspection found the
  separate generic constructions in Adjunction/Basic and ObjectProperty/FullSubcategory.
- `msearch.py ... grep "schemeDerivedDirectImage|twistedInverseImage|derived.*[Rr]ightAdjoint"
  AlgebraicGeometry`: zero hits in Mathlib.
- `rg` for `derived.*[Aa]djoint|schemeDerivedDirectImage|schemeDerivedQCoh` in the project's
  `lean/Sheaf` and upstream `WeilConjectures`: project derived categories and direct-image
  definitions are reusable; upstream hits concern étale/pro-étale coefficients and their
  different adjunctions, not D_QCoh(O_X) and this theorem.
- `grep -rn "lem-pc-noetherian-derived-direct-image-right-adjoint"` in upstream
  `WeilConjectures`: no hits. Searching `dag/lean_names_upstream.json` for derived/right
  adjoint names gave no exact declaration. The proposed declaration name is new.

Source verification: the local Stacks checkout is absent, so read
https://stacks.math.columbia.edu/tag/0A9E and https://stacks.math.columbia.edu/tag/08D5.
Tag 0A9E states existence on qcqs schemes; Tag 08D5 (1) states preservation for qcqs f.
The node's Noetherian specialization agrees. The source record has the historical 08DW
misreference already described in its review; use the corrected 08D5 from the proof/review.
This is a source-reference typo, not a fault in the statement. No statement correction,
new node, dependency module or disputed mathematical assertion is needed.

Validation: `scompile.py T1 lem-pc-noetherian-derived-direct-image-right-adjoint` compiled
the module on the server in 2.1 seconds, exit code 0, without errors or warnings.

## Second reading by T1

Independent reading of the node copy, its five statement-dependency nodes, their
recorded declarations, and the delivered Lean module. Verdict: the statement matches;
no Lean or node change is needed. Only this review section was appended.

Source checked first: the repository has no Stacks checkout. I downloaded the upstream
Stacks `duality.tex` and `perfect.tex` into this item's scratchpad and read
`lemma-twisted-inverse-image` (duality.tex:435–460), its surrounding section
(417–433), and `lemma-quasi-coherence-direct-image` (perfect.tex:443–459) with the
Total direct image section introduction. The former assumes qcqs source and target;
the latter's first clause assumes qcqs f. Neither section adds a base field,
properness, finite type, separatedness, or boundedness assumption. Their Noetherian
specialization is precisely the node. Also checked the rendered sources:
https://stacks.math.columbia.edu/tag/0A9E and
https://stacks.math.columbia.edu/tag/08D5. The node's source field retains the historical
08DW typo; its proof step 2 and prior review correctly identify 08D5. The delivered
docstrings already use 08D5. This does not require changing the mathematical statement
or a maintainer-owned source field.

Object, hypothesis and conclusion checklist (the list extracted from the node):

1. Objects X and Y are schemes: `{X Y : Scheme.{u}}`. Read Mathlib's `Scheme`, its
   local-affine field, and `Scheme.Hom` in the recorded Scheme module. These are
   schemes and morphisms of their underlying locally ringed spaces. MATCH.
2. X is locally Noetherian and quasi-compact:
   `[IsLocallyNoetherian X] [CompactSpace X]`. Read the class in Mathlib Noetherian:
   sections on every affine open are Noetherian; the immediately following
   `isLocallyNoetherian_of_affine_cover` identifies the node's covering formulation.
   `CompactSpace` means compactness of the whole underlying space with no separation
   condition (its docstring explicitly says so). MATCH.
3. Y has those same two hypotheses: `[IsLocallyNoetherian Y] [CompactSpace Y]`.
   Nothing stronger such as properness or Hausdorffness is assumed. MATCH.
4. A morphism f from X to Y: `(f : X ⟶ Y)`, not a morphism over an extra base.
   No geometric class is imposed on f. MATCH.
5. Derived categories of all O_X- and O_Y-modules: the two explicit
   `HasDerivedCategory.{wX}`/`HasDerivedCategory.{wY}` binders use exactly the shared
   `SheafOfModules.{u} (moduleRings _.toRingedSpace)` carriers. Read the dependency
   definitions and Mathlib DerivedCategory.Basic: `HasDerivedCategory` chooses a
   localization model, with `HasDerivedCategory.standard` supplying the standard
   universe model. These are structural choices, not extra geometric hypotheses.
   The definition uses complexes indexed by all integers, not bounded complexes. MATCH.
6. Rf_* is the existing `schemeDerivedDirectImage f`. Opened its definition and the
   underlying `RingedSpace.derivedModuleDirectImage`: the latter is the shared
   `moduleDirectImage g` right derived functor, computed by K-injective resolutions.
   The morphism is the underlying ringed-space morphism of the same f. MATCH.
7. D_QCoh is the full subcategory of objects with quasi-coherent cohomology:
   `schemeDerivedQCohCategory X`/`Y`, defined using `schemeDerivedQCohProperty`, which
   quantifies `∀ n : ℤ` over Mathlib's homology sheaves and `IsQuasicoherent`. MATCH.
8. First conclusion: Rf_* maps every object of D_QCoh(X) into D_QCoh(Y). It is
   `∃ h : ∀ E : schemeDerivedQCohCategory X,
   schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj), ...`.
   Read ObjectProperty.FullSubcategory: each E is exactly an ambient object together
   with its property proof. The preservation proof is concluded, not assumed. MATCH.
9. Second conclusion: the restricted functor has a right adjoint. The term
   `(schemeDerivedQCohProperty Y).lift
   ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) h`
   uses the existing full-subcategory inclusion and lift. Read both: lift retains
   the objects and morphisms of this composite and only packages the target property.
   Read `Functor.IsLeftAdjoint`: its field is
   `∃ right : D ⥤ C, Nonempty (left ⊣ right)`. Thus `.IsLeftAdjoint` has exactly the
   required direction and conclusion. The existential h then adjoint clause expresses
   both conclusions in their dependency order, without requiring a chosen adjoint. MATCH.

Edge cases: empty schemes and zero derived objects are admitted without any Nonempty
or nonzero binder. A morphism to the empty scheme is still quantified whenever it
exists. No field, characteristic, dimension, or natural-number parameter appears.
Degree zero and negative cohomological degrees are included by `∀ n : ℤ`.
Arbitrarily unbounded complexes and nonseparated Noetherian schemes are included.
There is no indexed-family restriction. The common scheme universe is the universe
of the recorded scheme category (both schemes can be placed in any common universe);
the localization hom universes wX and wY are independent. All three universes and
all variables are explicitly bound. No edge case excluded beyond the node hypotheses.

Independent H4 searches, using different conceptual words from the first worker:

- LeanFinder via msearch: "Grothendieck duality exceptional inverse image adjoint of
  pushforward for Noetherian schemes": eight hits, underived module pullback/pushforward
  and general site adjunctions; none states a right adjoint to Rf_* on D_QCoh.
- Loogle via msearch: `CategoryTheory.Functor.IsLeftAdjoint`: twelve hits, identifying
  the generic class and its adjunction constructions, not this geometric theorem.
- LeanSearch via msearch: "Grothendieck duality right adjoint derived pushforward quasi
  coherent sheaves": service returned Internal Server Error; recorded unavailable,
  with no mathematical search verdict inferred from that failure.
- Grep via msearch in AlgebraicGeometry:
  `twistedInverseImage|noetherian.*[Aa]djoint|pushforward.*IsLeftAdjoint`: two underived
  hits (Modules.Sheaf and Modules.Tilde), no exact match.
- Independently ran rg over project lean/Sheaf, upstream WeilConjectures, Mathlib
  AlgebraicGeometry, and dag/lean_names_upstream.json for twisted inverse image,
  exceptional inverse image, Noetherian adjoints and direct-image right adjoints.
  Upstream exceptional-inverse-image results are on étale/pro-étale coefficient
  categories, not O_X-modules. Project derived-image and D_QCoh definitions are
  exactly the imported dependency declarations. No duplicate of this theorem found.

H5/H6/H8/H9: no definitions in the delivery, hence no hollow data or private notion;
exactly one theorem, with `by sorry`. Both docstrings name the source and blueprint id;
the theorem docstring renders all six proof steps, including the preservation step
and Brown representability with the source and target direct sums. Imports are used,
there is no local notation/instance, private declaration, or hidden let/show binder.
The node's lean.statement is verbatim the source signature before `:=`.
No new nodes, dependency modules or statement corrections are in this delivery, so
H12/H13 and correction-citer checks have no additional cases. No mismatch found.

Validation by the second reader: the first server compile encountered a temporarily
missing SchemeDerivedDirectImage.olean in the T1 build view. The delivery dry run
subsequently passed both compilation and preflight (OK), and a fresh explicit scompile
of the same unchanged file succeeded in 2.2 seconds, exit code 0, no warnings or errors.
The transient build-view failure required no source or tool changes.
