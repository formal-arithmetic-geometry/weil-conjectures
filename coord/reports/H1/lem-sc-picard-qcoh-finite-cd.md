## Worker report

The module `Sheaf.AlgebraicGeometry.QuasicoherentFiniteCohomologicalDimension` states
`AlgebraicGeometry.Scheme.exists_quasicoherent_cohomology_bound`, with a single `sorry` proof.
No definitions or other theorems are introduced. The statement is unchanged.

Hypothesis and clause correspondence:

- A field k: `(k : Type u) [Field k]` (def-weil-field).
- A scheme X over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]` (def-pc-scheme).
  The class supplies the structure morphism `X ↘ Spec (.of k)`.
- X quasi-compact: `[CompactSpace X]`, the compactness of the underlying topological space;
  no Hausdorff assumption is imposed.
- Affine diagonal: `[IsAffineHom (pullback.diagonal (X ↘ Spec (.of k)))]`, exactly the
  relative diagonal over Spec(k) used in the node's proof. Over a field this is equivalent
  to the absolute affine-diagonal condition in Stacks 01XI (Spec(k) is separated).
- There exists a nonnegative integer d_X: `∃ d : ℕ`. Naturals encode exactly the
  nonnegative integers, without adding a further bound or choosing a cover in the statement.
- Every quasi-coherent O_X-module F: `∀ (F : X.Modules) [F.IsQuasicoherent]`.
  The quasi-coherence class is the Mathlib notion endorsed by pqf-def-coherent's module;
  finite type, finite presentation, and coherence are not assumed.
- Every degree p > d_X: `(p : ℕ), d < p →`. Since d is nonnegative, precisely the
  requested positive degrees are quantified; no degree zero vanishing is asserted.
- H^p(X,F)=0: `IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F)`.
  This is categorical zero in modules over O_X(X), equivalent to the zero group condition.
  The existential bound precedes both F and p, so it is uniform in F.

Dependencies and signatures were read with their docstrings:

- `Mathlib.Algebra.Field.Defs`, `Field` (class extending CommRing and DivisionRing).
- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (locally ringed spaces with affine neighborhoods, and locally ringed space morphisms).
- `Sheaf.AlgebraicGeometry.Coherent`, `AlgebraicGeometry.RingedSpace.IsCoherent`:
  its module explicitly delegates quasi-coherence to `SheafOfModules.IsQuasicoherent`
  in `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`, which is what this item uses.
  On schemes the local-presentation condition is the affine-local tilde condition in the node.
- `Sheaf.Topology.RingedSpaceModuleCohomology`,
  `AlgebraicGeometry.RingedSpace.moduleCohomology`:
  `(X : RingedSpace.{u}) (p : ℕ) : SheafOfModules.{u} (moduleRings X) ⥤
  ModuleCat.{u} ((moduleRings X).obj.obj (op ⊤))`, defined as the p-th right derived
  functor of global sections. `X.Modules` has exactly the required carrier.
  Added the existing landed node `def-sc-ringed-space-module-cohomology` to stmt_deps
  under STMT_DEPS MAY GAIN LANDED NODES; no new node or dependency replacement is needed.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`, `AlgebraicGeometry.IsAffineHom`:
  preimages of all affine opens are affine.

Source checked: https://stacks.math.columbia.edu/tag/01XI, Lemma 30.4.2 and its second
proof. The local coherent.tex is absent on this machine, so the source was read online.
Stacks gives vanishing in degrees at least the number of members of a finite affine cover;
this yields precisely the node's existential bound. The field is the node's specialization.
The docstring reproduces all three node proof steps and their dependencies (affine
intersections, alternating Cech complex, Cech comparison), with the empty-scheme case explicit.

Edge cases checked: empty X is permitted (take d=0; all its cohomology vanishes);
affine X permits d=0 without asserting H^0=0; p=d is excluded, p=d+1 included;
F=0 is allowed; arbitrary quasi-coherent modules are allowed, including those not of finite
type; all characteristics are allowed. No nonemptiness, Noetherian, finite-type,
separatedness, properness, or finite-dimensionality hypothesis was added. The scheme,
base field, and sheaf categories use the common arbitrary universe u of the pinned library.

Searches for existing statements (logged in searches.jsonl):

- LeanFinder: “A quasi compact scheme over a field with affine diagonal has uniformly
  vanishing higher cohomology for every quasi coherent module”: eight results on affine
  transition limits and quasi-compactness; no cohomology-bound statement.
- Loogle: `SheafOfModules.IsQuasicoherent, IsZero`: zero hits; unknown identifier IsZero.
- Mathlib grep via msearch.py: `cohomological.*dimension|finite.*cohom|vanishing`
  in AlgebraicGeometry: results concern vanishing ideals and affine limits, no matching theorem.
- LeanSearch: `finite cohomological dimension quasi coherent sheaves affine diagonal`:
  service unavailable (Internal Server Error); no verdict inferred from this failure.
- rg of WeilConjectures and lean/Sheaf for finite cohomological dimension and
  `moduleCohomology.*IsZero`: only unrelated etale curve cohomological dimension results;
  the existing ringed-space cohomology definition was found and reused.
- rg of WeilConjectures for the item id: no match. rg of Mathlib, source, project, and
  dag/lean_names_upstream.json for the proposed declaration: no existing declaration found.

Validation: scompile.py on the server succeeded (2.0 s), without warnings.
No statement fault or mathematical dispute found. Second reading is left to the dispatcher’s
independent reader; nothing has been delivered.


## Second reading by H1

I read the node copy and the Lean module independently, then all four statement
dependency records and their declarations. No statement correction, new definition
node, or dependency module is present. No mismatch requiring a Lean change was found;
the original statement and module are retained. This section is the only addition.

Object/hypothesis/conclusion inventory and correspondence (H3):

- Field k: `(k : Type u) [Field k]`. PASS: Mathlib `Field` extends `CommRing` and
  `DivisionRing`, matching def-weil-field, including nontriviality.
- Scheme X over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`. PASS: the recorded
  Mathlib `Scheme` is a locally ringed space with affine neighborhoods; `Scheme.Hom`
  is a locally ringed-space morphism. `OverClass.hom` supplies precisely the structure
  morphism `X ↘ Spec (.of k)`, with no finite-type or smoothness restriction.
- Quasi-compact X: `[CompactSpace X]`. PASS: this is compactness without Hausdorffness
  of its underlying space, precisely scheme quasi-compactness.
- Affine diagonal: `[IsAffineHom (pullback.diagonal (X ↘ Spec (.of k)))]`. PASS:
  `IsAffineHom` requires affine preimages of affine opens. The relative diagonal has
  domain X and codomain X ×_k X. Its affine condition is equivalent here to the
  absolute condition: absolute affineness implies relative affineness by base change;
  conversely compose the relative diagonal with X ×_k X → X × X, a closed immersion
  because Spec(k) is separated over Spec(ℤ), hence an affine morphism. Thus there is
  no hidden extra separatedness requirement on X.
- Nonnegative uniform bound: `∃ d : ℕ`. PASS: exactly a nonnegative integer;
  existential quantification precedes the module and degree, so d depends on X only.
- Arbitrary quasi-coherent O_X-module F: `∀ (F : X.Modules) [F.IsQuasicoherent]`.
  PASS: `Scheme.Modules` is `SheafOfModules.{u} X.ringCatSheaf`. The recorded Coherent
  module explicitly reuses Mathlib `SheafOfModules.IsQuasicoherent`, whose definition
  is local cokernel presentations between arbitrary free module sheaves, without
  finite-generation or finite-presentation conditions. On schemes this is the node's
  affine-local associated-module condition (Stacks 01IA). No private definition.
- Every degree p>d: `(p : ℕ), d < p →`. PASS: all relevant degrees are nonnegative;
  since d≥0, using naturals omits no requested degree.
- H^p(X,F)=0: `IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F)`.
  PASS: the recorded definition is the p-th right derived functor of global sections
  on O_X-modules, valued in O_X(X)-modules. `IsZero` there means the module is zero,
  equivalently its underlying additive group vanishes. Neither étale cohomology nor
  an unrelated abelian-sheaf Ext definition is substituted.

Source reading: the local Stacks directory is absent. I read the actual
[coherent.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex),
section `section-quasi-coherence`, label `lemma-vanishing-nr-affines` (Tag 01XI),
and its second proof. The section imposes no global Noetherian or field hypothesis;
the field is the DAG specialization. Its finite-cover estimate entails the node's
uniform existence conclusion. I also checked
[Stacks 01IA](https://stacks.math.columbia.edu/tag/01IA) for the quasi-coherence comparison.
The module docstring includes each of the node's three proof steps and all three
proof-dependency IDs. The empty-scheme branch avoids subtracting one from an empty cover.

Edge cases: PASS for empty X and an empty covering (d=0 suffices), zero F, and
arbitrary non-finite-type F. For affine X the permitted bound is d=0; p=0 is never
required to vanish. p=d is excluded and p=d+1 included. No characteristic, nonemptiness,
Noetherian, properness, finite-dimensionality, or separatedness assumption is present.
The arbitrary universe u is explicitly declared; it is the common universe used by
the pinned scheme/module definitions, and any larger objects can be accommodated by
increasing u. No independent small universe of test objects creates vacuous hypotheses.

Independent searches (H4), recorded by msearch in searches.jsonl:

- LeanFinder: “For every quasi-coherent module on a quasi-compact semi-separated scheme
  higher derived global sections vanish above a uniform bound”. Eight hits; derived
  category truncation and qcqs section localization results, no matching statement.
- Loogle: `"cohomology", "zero"`. Twelve hits: HomComplex cohomology classes,
  Ext comparison, continuous/group cohomology; none is scheme quasi-coherent vanishing.
  An earlier query without the comma was rejected by the parser and is not evidence.
- rg of Mathlib AlgebraicGeometry and ModuleCat/Sheaf, source WeilConjectures, and
  project lean/Sheaf using `semi.?separated`, `cohomology_bound`,
  `cohomological.?dimension`, `IsQuasicoherent.*IsZero`, and
  `IsZero.*moduleCohomology`: only unrelated étale/pro-étale results in the source;
  no duplicate. Also searched the full proposed name and item ID in source and
  dag/lean_names_upstream.json: neither is recorded there.
- The worker's LeanSearch service failure remains explicitly unavailable, not a
  successful negative search. The searches above provide independent semantic,
  name/type, and local-source checks.

H5/H6/H8/H9: one named theorem with `sorry`, no definitions and nothing proved;
source and blueprint tags occur in both docstrings. Each imported module serves a
recorded notion. All universes/variables are bound; line lengths are at most 100.
The node's lean.statement is verbatim equal to the signature in the file.
The added existing landed dependency def-sc-ringed-space-module-cohomology is permitted
by brief-stage2 §5, STMT_DEPS MAY GAIN LANDED NODES. No other DAG fields changed.

Validation: independent server scompile.py succeeded without warnings. Delivery
preflight and its server compilation are run after this report is appended.
