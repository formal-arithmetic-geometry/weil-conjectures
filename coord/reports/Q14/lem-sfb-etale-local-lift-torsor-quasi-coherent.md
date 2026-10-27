## Worker report

This is a stage-2 statement delivery of the accepted stage-1 split. The inherited
stage-1 rejection is inapplicable, as coord/brief-stage2.md §0 now explicitly
explains. The live node is split, has a passing stage-1 review, is in the stage-2
queue, has no Lean attachment, and has no released repair note. Its statement,
proof, dependencies, source, and other fields are unchanged; only `lean` is added.

The module is `Sheaf.AlgebraicGeometry.EtaleLocalLiftDerivationAction`, namespace
`AlgebraicGeometry.Scheme.InfinitesimalLifts`. The main declaration is
`exists_derivationAction`. Its objects have actual definitions, and the two
postponed theorems have `sorry` proofs. `isLift_precomp` is the restriction-stability
component needed to define the lift subpresheaf; its docstring gives the entire
pullback argument. Both it and the main theorem are recorded in lean.declarations.
The remaining helpers belong to the lift/coefficient/action notions explicitly
introduced in the item's own statement, rather than to independent new notions.

Hypothesis and clause correspondence:

- Schemes V, W, T₀, T and their morphisms are `{V W T₀ T : Scheme.{u}}`,
  `f`, `i`, `a₀`, `b`. The finite-presentation hypothesis is the exact Mathlib
  `[LocallyOfFinitePresentation f]`. No affine, separated, smooth, Noetherian,
  flatness-of-a₀, or nonemptiness hypothesis is imposed.
- The first-order thickening is `hi : IsFirstOrderThickening i`, whose definition
  is `IsClosedImmersion i ∧ i.ker ^ 2 = ⊥`. The commutative square is
  `comm : a₀ ≫ f = i ≫ b`.
- The ideal on T is the existing `i.ker.toModules`. Its module on T₀ is
  `idealOnReduction i := (tensorPullback i).obj i.ker.toModules`: this is the
  canonical conormal I/I², hence I with the quotient scalar action because I²=0.
  This uses the actual tensor construction, not a chosen module of the right size.
- E is `((tensorPullback a₀).obj f.relativeDifferentials)`.
  `coefficients f i a₀` is exactly `(pushforward i).obj
  (SheafOfModules.homObj (R := T₀.sheaf) E (idealOnReduction i))`.
  The existing internal Hom consists, on an open, of linear natural maps on the
  over-category of smaller opens, which are precisely the restricted sheaf maps.
  Pushforward supplies the quotient scalar action through i.app. The first
  conjunct of the main theorem is its `IsQuasicoherent` property.
- An arbitrary object `U : T.Etale` gives U.hom : U.left → T. The module uses
  `pullback i U.hom`, with fst to T₀ and snd to U.left. `IsLift` states both
  `a ≫ f = U.hom ≫ b` and
  `pullback.snd i U.hom ≫ a = pullback.fst i U.hom ≫ a₀`, in that order.
  `liftSubfunctor` is literally the subfunctor of the representable functor on
  this étale category given by these two equations. `liftPresheaf` is its
  subtype-valued functor, with actual precomposition as its maps. The main
  theorem's second conjunct is `Presheaf.IsSheaf T.smallEtaleTopology` for this
  very presheaf, with no sheafification or change of its section sets.
- H_et is the dependency's `etaleTensorSectionsSheaf H`: its value and restriction
  maps are definitionally `Γ((tensorPullback U.hom).obj H, ⊤)` and
  `etaleTensorSectionsRestriction H v`. Those exact expressions occur in
  `DerivationAction.act` and `.naturality`. These expressions also make sense
  before proving quasi-coherence, so the action structure needs no chosen
  quasi-coherence instance. The first conjunct supplies that instance to package
  the already fixed coefficient presheaf as the recorded associated étale sheaf.
- Existence of the sheaf action is `Nonempty (DerivationAction f i a₀ b)`.
  The fields `zero_act` and `add_act` are the additive action laws, and
  `naturality` is precisely compatibility with every étale restriction.
  `simply_transitive : ∀ U a, Function.Bijective (fun h ↦ act U h a)` says the
  orbit map is bijective whenever a lift a is supplied. It does not supply a lift.
- `CoefficientComparison.ideal` is the flat-base-change identification of
  u₀*I with the actual ideal of U₀ in U. `.hom` identifies u*H with the
  pushed-forward internal Hom on U₀. The two evaluation fields normalize these
  comparisons on pulled-back local sections, with arbitrary smaller opens Q.
  Thus they are the actual base-change comparisons, not arbitrary isomorphisms.
  The equations express s ↦ 1 tensor s and h ↦ 1 tensor h on local generators;
  tensor linearity and local generation determine the maps throughout.
- `DerivationAction.same_base` states equality of the continuous maps of a and
  its translate, as follows already from reduction along a first-order thickening.
  The last field `formula` evaluates on every ring section x over every open P
  of V and every Q contained in the preimages under both lifts. It applies the
  universal `relativeDifferentialsDerivation` to x, pulls it back by u₀≫a₀,
  uses `tensorSectionsComp.inv` to obtain u₀*a₀*Ω, evaluates the coefficient
  homomorphism, and includes its value into O_U by `.ideal` and the existing
  ideal inclusion. It sets c.appLE(x) equal to a.appLE(x) plus precisely this
  term. This is a^sharp+D, with the required positive sign. The auxiliary
  inclusion witnesses hg and ht merely type the restrictions of those sections;
  they are not additional hypotheses on the geometric data. `@id Γ(U.left,Q)`
  only resolves the definitionally equal ring/module carriers for addition.
- No local or global existence is asserted. In particular the theorem never
  quantifies over an inhabited lift type, supplies an étale covering with lifts,
  or asserts `Nonempty ((liftPresheaf ...).obj U)`.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.Thickening`:
  `AlgebraicGeometry.IsFirstOrderThickening`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSection`, and its uniquely
  section-normalized adjunction. The tensor functor itself is the publicly
  imported upstream construction, not a duplicate. The coefficient restrictions
  use upstream `tensorSectionsComp`, whose adjunction is likewise normalized.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsDerivation`, and the
  existing `relativeDifferentialsHomEquiv` for the proof plan.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: recorded module of
  pqf-def-coherent. For the quasi-coherence clause actually needed here it
  publicly imports Mathlib's `SheafOfModules.IsQuasicoherent`; its combined
  finite-type predicate is not substituted for quasi-coherence.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and
  `Scheme.Etale`, publicly available from the coefficient-sheaf module.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, available from the scheme/site dependencies.
- `WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf`:
  `Scheme.Modules.etaleTensorSectionsSheaf`, with underlying
  `etaleTensorSectionsPresheaf` and `etaleTensorSectionsRestriction` as above.
- The recorded ideal and Hom constructions are
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `Scheme.IdealSheafData.toModules`, `toModulesι`; and
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`. No second notion is defined.

All already stated proof-dependency modules are imported (plain imports for proof
inputs), including the Mathlib matches for flat exactness, finite presentation of
Kähler differentials, affine Hom base change, representable fpqc descent, covering
axioms, and maps into Spec. `lem-sfb-relative-differentials-sheaf-universal-property`
has no Lean record or mathlib_match, so no nonexistent module is imported. Its
universal bijection is already available from the imported upstream
`relativeDifferentialsHomEquiv`; no new statement dependency is needed to type
this theorem. The seven proof steps are written in the main docstring, including
all the DAG inputs and the square-zero addition/subtraction argument.

Edge cases checked before drafting and again against the final statement:

- I=0: the conormal is zero, H=0, and reduction is an isomorphism. Each lift set,
  when inhabited, is a singleton. The action and formula have this behavior.
- f=id: Ω=0, and the square determines the unique compatible lift; again H=0.
- U empty and T empty: the set of maps from the empty scheme and the section
  groups are singletons; no nonempty-scheme assumption was introduced.
- A genuinely obstructed lift problem is allowed: over k, use
  V=Spec(k[x]/(x²)), T=Spec(k[ε]/(ε³)), T₀=Spec(k[ε]/(ε²)), and a₀(x)=ε.
  The thickening ideal (ε²) has square zero. Every putative image
  ε+cε² has square ε²≠0, so no global lift exists. Our theorem still asserts only
  an action on the empty lift set, and its orbit clauses are vacuous there.
- For affine line and a square-zero ideal, the normalized formula gives literal
  translation by an ideal-valued derivation with positive sign.
- No finite-free hypothesis on E or torsion condition on I occurs. Local finite
  presentation of f ensures E is finitely presented, even for a nonflat a₀.
- All schemes have the explicitly bound universe u. Their étale category retains
  its natural object universe u+1 and morphism universe u; no equality between
  those site universes is imposed. All opens and coefficient modules have the
  usual universe u, and lift sets have universe u.

Searches:

- `msearch.py ... leanfinder`: “The sheaf of compatible scheme lifts across a
  square zero thickening is acted on simply transitively by Hom of relative
  differentials into its quasi coherent ideal” returned eight results: the
  presheaf differential construction, FormallyUnramified, and
  Algebra.Extension.homInfinitesimal. These do not state a sheaf action or its
  coefficient quasi-coherence.
- `msearch.py ... loogle 'Derivation, KaehlerDifferential'` returned ring-level
  Kähler differential universal properties and derivation identities, including
  `KaehlerDifferential.linearMapEquivDerivation`; no scheme lift sheaf theorem.
- `msearch.py ... grep 'lift.*[Tt]orsor|[Ll]iftPresheaf|[Ll]ift.*[Dd]erivation'
  AlgebraicGeometry` returned zero Mathlib matches.
- `rg` in both live `lean/WeilConjectures` and `lean/Sheaf` for first-order,
  lift-presheaf, infinitesimal-lift, and lift-torsor names found deformation
  Ext-torsor material (`SchemeSquareZeroLiftTorsor`) concerning flat deformations
  of schemes, not this theorem about maps to a fixed scheme. The source has the
  reusable tensor pullback, ideal, internal Hom and universal differential
  definitions used here. No matching lift-presheaf/action declaration was found.
- Exact-id searches in both Lean trees and dag/lean_names_upstream.json found no
  existing declaration. The historical lem-per node has the same prose but no
  Lean record or mathlib_match and is on the dropped route; it supplies no
  declaration to reuse. Its existence does not turn this into an existing match.

Sources read locally: spaces-more-morphisms.tex, sheaf/action/special-case
lemmas (061A, 061C, 061D), and more-morphisms.tex, difference-derivation,
equation-D, action-by-derivations and the pseudo-torsor argument in the smooth
criterion. These give exactly the scheme special case in the accepted node.
No statement dispute, correction, new node, or dependency repair is needed.

Validation: the prescribed scompile.py compiled both its scratch module and the
actual library-path module with no errors or warnings. Every proof is sorry;
every definition and structure has real data. No live file, direct Git command,
global build, or local compile outside the prescribed wrapper was used.

## Second reading by Q14

The worker reread the complete node, final Lean file, and its imported
coefficient signatures for a final clause audit; the independent review is the
maintainer's, as the current brief specifies (no other agents were started).
This paragraph does not claim an independent worker review.

The geometric hypotheses match one for one, including arbitrary T rather than
just affine T. The reduction equation uses snd to U and fst to T₀. Quasi-coherence
is asserted for the actual pushed-forward Hom, not assumed, and no existence of
a lift has entered the action structure. The objectwise coefficient group and
its restriction are exactly those in the recorded associated étale sheaf. The
coefficient comparisons have section normalizations, and the local formula uses
the universal differential of x, not an arbitrary map or an unconstrained
identification. The formula fixes the positive action convention. The identity,
empty, and obstructed cases remain included. The only changes during elaboration
were the full scheme-forgetful functor in the lift subfunctor and explicit
identity coercions between the equal ring/module carriers in the final formula;
these affect neither objects nor hypotheses. The item node is unchanged outside
its lean record.
