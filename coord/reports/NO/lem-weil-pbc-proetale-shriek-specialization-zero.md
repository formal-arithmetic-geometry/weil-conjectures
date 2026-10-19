## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero` states
`AlgebraicGeometry.Scheme.ProEt.shriek_sections_subsingleton_of_specializes_closed`,
with its sole proof `sorry`. No definition, new node, dependency replacement, or statement
correction is needed. Source read: literature/stacks-project/proetale.tex,
lemma-jshriek-zero (Tag 09AG), including its proof.

Hypotheses and clauses, in order:

- Schemes and weakly etale `j : U → X`: `{X Z : Scheme.{u}} (U : X.ProEt)`.
  The bundled scheme is `U.left`, the arrow is `U.hom`, and weak etaleness is `U.prop`.
  This ranges over every weakly etale arrow in the node's fixed scheme universe.
- Closed immersion: `(i : Z ⟶ X) [IsClosedImmersion i]`.
- Empty intersection: `hdisjoint : IsEmpty ↥(pullback U.hom i)`.
  This is emptiness of the underlying space, including all scheme-theoretic empty fibres.
- Affine object over X: `(V : X.ProEt) [IsAffine V.left]`.
- Every point specializes into the closed fibre: `∀ v : V.left,
  ∃ z : ↥(pullback V.hom i), Specializes v ((pullback.fst V.hom i) z)`.
  The projection image is exactly the underlying closed fibre; the order of Specializes
  is from the original point to its specialization.
- Arbitrary abelian sheaf on U: `G : Sheaf (topology U.left) AddCommGrpCat.{u + 1}`.
  The coefficient universe contains all site object and arrow data.
- The displayed direct-sum presheaf is expressed by the existing Mathlib construction
  `(MorphismProperty.Over.map ⊤ U.prop).op.leftKanExtension G.obj`.
  This is not an arbitrary left adjoint or a replacement object. At W the indexing
  costructured-arrow category decomposes into components indexed by lifts W → U over X.
  Each component has terminal object the lift itself, considered as an object of
  U.ProEt (weakly etale by cancellation). Consequently its colimit is exactly the
  coproduct of G(W → U), with restriction sending each lift to its composite.
  Read the full construction of SmallSite.LiftIndex, its discreteFunctor,
  toDiscreteAdjunction, and final_discreteFunctor in
  WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension.
  Those constructions do not require monomorphisms; only the later specialized
  shriek API adds that hypothesis. General Kan extension existence here is supplied
  by Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize; no extra hypothesis
  is introduced. Thus the formula in the node is encoded using an existing canonical
  construction rather than a second definition of its presheaf.
- Abelian sheafification is `sheafify (topology X)` on this AddCommGrpCat-valued
  presheaf, the underlying presheaf of `presheafToSheaf`.
- `(j_! G)(V) = 0` is `Subsingleton` of that abelian group's carrier, equivalent to
  every element being zero. No vanishing of a bare Type as categorical IsZero is used.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and its morphisms.
- Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale: AlgebraicGeometry.WeaklyEtale.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: AlgebraicGeometry.IsClosedImmersion.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback and pullback.fst.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and Scheme.ProEt.topology.
- Mathlib.CategoryTheory.Sites.Sheafification: presheafToSheaf, sheafify.
- Mathlib.CategoryTheory.Sites.SheafCohomology.Basic: Sheaf and the recorded H' framework;
  this import supplies the stated dependency's shared site/sheaf setting, not a cohomology
  hypothesis.
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization: weaklyEtale_localization,
  including the scheme-preserving slice equivalence, sheaf equivalence, and cancellation.
- Sheaf.CategoryTheory.ExtensionByZeroPresheaf: SheafOfModules.extensionByZeroPresheaf,
  its summand and restriction constructions. It is the ringed-module construction; the
  abelian statement uses the existing Kan-extension spelling of the same sum rather
  than imposing a ring or module structure on G. Imported for the proof dependency.

Other stated proof dependencies are imported through SiteSheafificationSectionsLocal,
UniversallyOpen (Flat.generalizingMap), GammaSpecAdjunction (Spec.reflective), and
ClosedImmersion. The underlying-set sheaf equivalence and affine-morphism instances
are available transitively. The arbitrary-ideal specialization-localization proof
node has no recorded Lean module yet, so there is no module to import for it.
All five proof steps, including empty local objects, are in the theorem docstring.

Edge cases checked: empty U, V, X, Z; V empty gives the empty-cover vanishing;
Z empty forces V empty under hspecializes; nonempty localized objects have no lift to U,
whereas an empty localized object has a unique lift but G has zero sections there.
No noetherian, ideal finiteness, quasi-compactness of j, open immersion, monomorphism,
torsion, or coefficient restriction was added. The affine V hypothesis is retained.

Searches performed (msearch.py NO with this item id):

- leanfinder: "Extension by zero of an abelian sheaf on the pro-etale site vanishes
  on affine objects specializing into a disjoint closed subscheme". Eight hits,
  concerning structure-sheaf sections at scheme limits and zero on open covers;
  none is this theorem.
- loogle: `"sheafify", "zero"`. Two hits, PresheafOfModules.Sheafify.zero_smul
  and smul_zero; neither is this theorem.
- grep Mathlib CategoryTheory: `shriek|extensionByZero|extension_by_zero`. Zero hits.
- rg in the full upstream WeilConjectures tree for the item id: no hit.
- rg in upstream pro-etale files and project Sheaf sources for shriek/extensionByZero:
  found open-immersion/compactification shriek and the ringed-site presheaf dependency,
  but no specialization-zero statement. Read the exact side-framework
  FiniteCoefficient.LowerShriek.Open.Defs and UpperLowerStar.Defs and
  coord/pefw-upstream-framework.md. localizationLowerShriek requires Mono f, hence
  cannot be used for the arbitrary weakly etale j of this node.
- Read the existing Kan-extension construction and its pointwise existence instance;
  this gives the full direct-sum presheaf without a substitute notion.
- rg for the chosen declaration name and specialization/shriek combinations in both
  project and upstream sources: no existing matching statement or name collision.

Validation: scompile.py on the server, nice 19, two threads, 60 seconds per file.
The initial compile diagnosed a missing carrier coercion on pullback schemes;
explicit `↥` fixed it. The next compile was clean. Final preflight recompiles the
completed module. No local compiler or lake build was used.


## Second reading by NO

Read the node and its nine statement dependencies, their recorded signatures and
source modules, and Stacks proetale.tex, section Extension by zero, definition-extension-zero
and lemma-jshriek-zero (Tag 09AG), including the proof. The section imposes no
Noetherian, quasi-compactness, monomorphism, or coefficient hypothesis. There is no
statement_change, new definition node, or dependency module in this delivery.

Object/hypothesis/conclusion checklist, in the node's order:

1. Schemes X, U, Z and weakly etale j: `{X Z : Scheme.{u}} (U : X.ProEt)`
   supplies j as `U.hom`, with source `U.left` and `U.prop : WeaklyEtale U.hom`.
   Read Mathlib's `Scheme.ProEt = MorphismProperty.Over @WeaklyEtale ⊤ X` and
   `WeaklyEtale` (flat morphism and flat diagonal). Verdict: exact; the bundle
   introduces no restriction beyond the node's small-site size convention.
2. Closed immersion i: `(i : Z ⟶ X) [IsClosedImmersion i]` uses the recorded
   class (closed embedding with surjective stalk maps). Verdict: exact.
3. Empty intersection: `(hdisjoint : IsEmpty ↥(pullback U.hom i))` is emptiness
   of the underlying scheme of U times_X Z. Read the recorded `pullback` and its
   projections; no reducedness or scheme-theoretic substitute is imposed. Verdict: exact.
4. Affine object V over X: `(V : X.ProEt) [IsAffine V.left]`. This requires the
   source scheme to be affine, as the source does; it does not merely assert that
   its structure morphism is affine. Verdict: exact.
5. Every point specializes into V_Z: `hspecializes : ∀ v : V.left,
   ∃ z : ↥(pullback V.hom i), Specializes v ((pullback.fst V.hom i) z)`.
   The first projection identifies its image with the closed fibre; `Specializes`
   runs from v to its specialization. Swapping the source's written Z times_X V
   with V times_X Z just exchanges the canonical projections. Verdict: exact.
6. Every abelian sheaf G on U_proet: `(G : Sheaf (topology U.left)
   AddCommGrpCat.{u + 1})` uses the recorded site and abelian-sheaf definitions.
   There is no ring, torsion, finite generation, or constructibility condition.
   Verdict: exact under the recorded u/u+1 size convention.
7. The specified direct-sum presheaf: `(MorphismProperty.Over.map ⊤ U.prop).op.
   leftKanExtension G.obj`. Read the full LiftIndex construction in upstream
   CategoryTheory/GrothendieckAbelian/HasLeftKanExtension.lean, especially
   `toOver`, `ofCostructuredArrow`, `homCostructuredArrow`, `discreteFunctor`,
   `toDiscreteAdjunction`, and `final_discreteFunctor`. At W, the comma category
   maps to the discrete type of lifts W → U over X; its right adjoint includes
   one terminal object per component, with value G(W → U). Thus the colimit is
   the coproduct of precisely these values; restriction composes each lift with
   the restricting arrow and uses G's restriction. Weak etale cancellation gives
   each lift its U-site object. These constructions require no Mono hypothesis.
   General colimit existence supplies the Kan extension, with no extra binder.
   Verdict: the same presheaf, not an arbitrary adjoint or a private replacement.
8. Abelian sheafification: `sheafify (topology X)` on this presheaf. Read the
   Mathlib abbreviation: it is exactly the underlying presheaf of
   `presheafToSheaf`, not set-valued sheafification. Verdict: exact.
9. Vanishing at V: `Subsingleton ((sheafify ...).obj (op V))`. This is the
   carrier of an abelian group, so it says every section is zero. Quantifiers
   and hypotheses precede this assertion exactly as in the node. Verdict: exact.

Dependency and uniqueness check: read the existing module extension-by-zero presheaf;
it is genuinely the ringed-module construction and cannot be applied directly to
an arbitrary AddCommGrpCat-valued G. The existing categorical Kan extension already
gives the abelian sum; a new definition is unnecessary. Read the exact group-clone
FiniteCoefficient/UpperLowerStar/Defs.lean and LowerShriek/Open/Defs.lean and
coord/pefw-upstream-framework.md. The named `localizationLowerShriek` is under
`[Mono f]`; using it here would add a hypothesis absent from 09AG. The chosen
statement correctly uses the underlying general construction. The localization
dependency's equivalence preserves underlying schemes and arrows, as its full
signature explicitly records. No unusable dependency or missing notion remains.

Independent searches with different terms: msearch leanfinder query "Abelian sheaf
left Kan extension vanishes on schemes specializing to a disjoint closed subscheme"
returned eight hits about structure-sheaf sections and skyscraper stalks, none this
statement. Loogle `"Specializes", "Subsingleton"` returned zero hits. LeanSearch
query "Proetale extension by zero vanishes when every point specializes into a
disjoint closed subscheme" was recorded unavailable (Internal Server Error).
Independent rg across Mathlib, upstream WeilConjectures, and project lean/Sheaf for
shriek/Kan-extension with specialization/subsingleton, and the exact declaration
name, found no matching theorem. Read the existing named shriek definitions rather
than inferring their applicability from their names.

Edge cases: empty X, U, Z, and V are allowed, and the zero sheaf is allowed. If
Z is empty, hspecializes forces V empty; if V is empty, its empty covering forces
zero sections. Empty localized objects have a lift to U but G's sections there
are zero, as docstring step 4 explicitly records; nonempty localized objects have
no lift. The coproduct therefore handles both empty and nonempty lift sets.
There is no n, characteristic, field, or finiteness parameter to exclude an edge
case. `universe u` is bound and the coefficient universe u+1 agrees with the
recorded site/sheafification convention; all variables are explicitly bound.

H5/H6/H8/H9: no definition is added; the only theorem has proof `sorry`.
Both docstrings name Tag 09AG and the blueprint id. Its five numbered proof
steps track all five DAG proof steps, including local representatives, finite
affine refinement, arbitrary-ideal localization and flat generalization lifting,
no-map/empty-object vanishing, and sheaf uniqueness. Imports provide the statement
and the available recorded proof dependencies. No file-local notation, instance,
private definition, or line exceeding 100 characters occurs. The node's
lean.statement is verbatim the file signature.

Mismatches and repairs: none. Preserved the Lean file and node unchanged; added
this independent reading and its search evidence only. Validation below uses only
scompile.py on the server (nice 19, two threads, 60 seconds per file).
