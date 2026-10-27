## Worker report

The module Sheaf.CategoryTheory.SheafDgModuleLocalization defines the complete notation of
this definition node in namespace CategoryTheory.SheafDg. The node statement is unchanged.
All definitions have actual terms. Named construction obligations have whole-proof `sorry`,
source/proof docstrings, and are listed with the definitions in lean.declarations on this
owning node. They assert only the laws needed by these constructions, not existence of a
left derived extension. In particular DerivedExtension is supplied data, never chosen from
an existence theorem.

Clause-by-clause correspondence:

- Size convention: explicit universe levels u, v, w, a site C : Type u with Category.{v},
  and EssentiallySmall.{w} C. For topological local perfectness C is Opens X. Ring and
  module sections are in w; no equality of the site object and morphism universes is imposed.
  The word localization's Hom universe includes the object universe, providing the larger
  universe specified in the node. Ordinary D(S) has its explicit HasDerivedCategory input.
- X and the commutative coefficient sheaf: the general-site construction takes
  S : Sheaf J CommRingCat.{w}. IsLocallyPerfect specializes this to TopCat.Sheaf on X.
  rings S is the underlying ring sheaf; Complex S uses ringedSiteModules of that sheaf.
- Integer cochain complex, associative unital bilinear multiplication, and Leibniz rule:
  Algebra S = Mon (Complex S). The ambient tensor is the sheaf tensor's direct-sum total
  tensor; multiplication being a chain map is exactly d(ab)=d(a)b+(-1)^|a| a d(b).
  Mon imposes associativity and the two-sided unit. No graded commutativity is imposed.
- Left module, unital associative bilinear action and its Leibniz rule: LeftModule A is
  Mod (Complex S) A.X. Its structure map is a chain map A tensor M to M. Morphisms are
  Mathlib Mod.Hom, so are degree-zero chain maps with the action-preservation equation.
- Degree-r maps: GradedMap A M N r is the subtype of HomComplex.Cochain with GradedLinear.
  This says h(am)=(-1)^(r p) a h(m) as a sheaf-map equality for every p,q. The HEq only
  transports associativity of the integer degree indices; it is not an extra hypothesis.
- Homotopies and K: homotopyRel asks for an underlying Homotopy f.hom g.hom whose
  degree-minus-one cochain is GradedLinear. Mathlib Homotopy gives f-g=dh+hd. Homotopy A
  is CategoryTheory.Quotient of this relation; q is its actual quotient functor.
- Cohomology and W: cohomology descends the underlying complex homologyFunctor using
  Homotopy.homologyMap_eq. quasiIsomorphisms asks IsIso of every integer cohomology map.
- D_X(A) and Q_A: Derived A is quasiIsomorphisms.Localization, not an unspecified category.
  Mathlib Localization.Construction builds paths in the quiver of arrows and W-inverses,
  then quotients by identity, composition and the two inverse relations. Q is that Q.
- Shift degrees/differential/action: shift uses the actual M.X[k] and its unique action
  satisfying IsShiftAction, with (-1)^(k p) on algebra degree p. Mathlib's complex shift
  uses M^(i+k) and differential (-1)^k d. The construction obligation uniquely determines
  the action on this fixed complex; it does not choose an undetermined module.
- Cones: cone uses the actual CochainComplex.mappingCone f.hom. IsConeAction fixes both
  projections to the target action and the signed shifted source action. Mathlib's order
  is M[1] plus N; its two projections identify it with the node's N plus M[1]. Its
  differential is exactly (d_N n+f m,-d_M m). coneIn is mappingCone.inr; coneConnecting
  is mappingCone.triangle.mor3, defined from the negative fst cocycle. coneTriangle
  localizes these maps and uses the specified shift comparison. IsConeTriangle includes
  exactly the triangles isomorphic to these. No triangulation theorem is asserted.
- Forgetful functor: forgetHomotopy forgets the action and descends via ordinary homotopy;
  forgetBeforeLocalization composes with DerivedCategory.Qh. forget is the actual
  Localization.Construction.lift, sending W-inverses to the inverse underlying derived map.
- Restrictions: restrictionComplex is SheafOfModules.overFunctor on complexes.
  restrictAlgebra and restrictModule use the actual restricted complexes and uniquely
  characterized actions on every slice section, as IsRestrictedAlgebra/IsRestrictedAction
  state. The unit is uniquely determined by the restricted multiplication's unit laws.
  restriction uses the actual restricted chain maps; derivedRestriction is the unique
  functor with that exact factorization through moduleQ. For Opens X, C/U is equivalent
  to Opens U, so this is restriction to the open space with all sheaf structure maps.
- Local perfectness: IsPerfect is the intersection of all ObjectProperty subcategories
  satisfying IsPerfectClosure. That predicate contains regular A and closes under
  isomorphisms, finite coproducts (all Fin n, including 0), every integer derived shift,
  the specified cones, and explicit retracts i followed by r equal to identity.
  In this additive derived category finite coproducts are finite direct sums.
  IsLocallyPerfect quantifies over a set of opens covering every point, and applies
  IsPerfect after the specified derivedRestriction on every member of that cover.
- A multiplicative unital degree-zero coefficient-linear chain map is A ⟶ B in Mon
  (Complex S). restrictScalars is exactly Mod.comap φ.hom; its complex is unchanged.
- Ordinary extension: extensionObj is the coequalizer IN B-modules of balanceLeft and
  balanceRight from the free B-module on A tensor M to the free B-module on M.
  Their underlying formulas are (b φ(a)) tensor m and b tensor (a m). This gives the
  sheafified balanced direct-sum total tensor. Its differential is inherited from the
  total tensor and its B-action is on the first factor. No commutative-dg-algebra
  hypothesis was added (the upstream Mod.extendScalars requires that, so is not used).
  extensionMap is uniquely specified after the quotient projection. extension is its
  functor; extensionBar descends extension followed by moduleQ through homotopies.
- Conditional left derived extension: DerivedExtension φ has functor LF, comparison
  Q A followed by LF -> extensionBar φ, and for EVERY V the exact bijectivity of
  η -> whiskerLeft (Q A) η followed by comparison. No resolution hypothesis, adjunction,
  existence theorem or substitute arbitrary isomorphism is supplied.
- Specified action counit: actionCounit is uniquely specified by its composite with the
  quotient projection being the free-module action map b tensor n -> bn.
  derivedActionCounit is comparison at q_A Res N followed by moduleQ_B of actionCounit,
  with exactly the source and target in the node.

Dependency declarations read and used:

- def-weil-size-convention is metatheoretic, with no declaration; explicit levels and
  EssentiallySmall implement it as its record instructs.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules, the transparent
  Mathlib SheafOfModules abbreviation, for every underlying complex.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory, HasDerivedCategory,
  DerivedCategory.Qh; HomologicalComplex.homologyFunctor for cohomology sheaves.
- Mathlib.CategoryTheory.Triangulated.Basic: Pretriangulated.Triangle and Triangle.mk.
- def-pc-tensor-complex-sheaves: HomologicalComplex.tensorObj (the monoidal form of
  CochainComplex.mapBifunctor with curriedTensor), ιTensorObj, with the monoidal structure
  from Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses and Mathlib Monoidal.
  That module retains the existing SheafOfModules.monoidalCategory localization tensor,
  rather than making a new tensor, and supports independent site universes.
- Mathlib Mon/Mod, Quotient, Localization.Construction supply the actual categories.
  WeilConjectures.CategoryTheory.ModuleObjects.Abelian supplies free-module functors and
  finite coequalizers without a commutativity assumption on A.
- WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal supplies the existing
  module_overFunctor_preservesZero; no private copy is made.

Searches (2026-10-24):

- msearch.py leanfinder: "Sheaves of left differential graded modules homotopy localization
  and derived extension of scalars" returned ordinary DerivedCategory.Qh, linearity and
  derived-functor localization results, no sheaf dg module category.
- msearch.py loogle: "ModuleCat, Mon_" returned unknown identifier Mon_, no match.
- msearch.py leansearch: "sheaf differential graded module category localization" returned
  SheafOfModules, its maps, ordinary sheafification localization and HasDerivedCategory;
  none has dg actions or the signed left-module homotopy relation.
- msearch.py grep: "DifferentialGraded|dgModule|DGModule|DgModule" returned no Mathlib hits.
- rg on lean/WeilConjectures and lean/Sheaf for dgModule, DGModule, DgModule,
  DifferentialGraded, dg.module and the item id found the right-module implementation
  CategoryTheory.DgAlgebra.RightModule over complexes of integer modules and its homotopy
  and cone modules. These are different coefficient objects and right actions, and do
  not define sheaf left dg modules. Read DgAlgebraDerivedCategory, DgAlgebraHomotopyStructure
  and DgModuleConeCalculus in full. Read the monoidal/Mod/quotient/localization source APIs.
- rg found and reused the independent-universe sheaf tensor and existing restriction API.
  tools/blueprint_refs.py ancestor reports None (as the inherited node already records).

Edge cases checked before writing and on the final signatures:

- No boundedness on complexes or degrees; all p,q,r,k,n are arbitrary integers.
- Odd p with shift k=1 gives the minus left action; r=-1 gives the odd-degree homotopy
  sign. The cone's connecting map is NEGATIVE projection, confirmed in Mathlib's
  HomotopyCategory/Pretriangulated source definition of mappingCone.triangle.
- Empty finite sum is included by n=0; the zero module and zero coefficient algebra are
  allowed by Mon/Mod. A retract is i followed by r, with no accidental r followed by i.
- The empty space admits the empty open cover. Covers are arbitrary sets of opens,
  not finite covers. Open restriction does not impose nonemptiness.
- The action counit is defined for every B-module N, including zero, with its restricted
  A-action. Identity and zero algebra maps, when unital, use the same balancing formulas.
- Coefficients and site sizes remain independent within the explicit size bound. There
  is no equality identifying site object and morphism universes.
- DerivedExtension is a type of specified data, not a theorem claiming those data exist.

No statement correction, disputed statement, dependency record repair, or new notion node.
Compilation through scompile.py succeeded in both sandbox and module-path modes. Final
import pruning and delivery preflight are recorded below when complete.

## Second reading by Q27

No other worker was started, as the dispatcher brief forbids sub-agents. The maintainer's
independent review is the independent reading. The worker's final self-audit matched every
clause above to the node and file. It confirmed the left-module Koszul signs, projection
order, and negative connecting map against the source. It removed unused imports of the
commutative-algebra scalar-extension API and the generic derived-functor API. It retained
only concrete balancing coequalizers and the node's exact natural-transformation bijection.

Construction obligations left as named theorem sorries (all in the owning node record):

`complexMonoidalPreadditive`, `complexTensorPreservesFiniteColimits`, `existsUnique_shiftAction`, `shiftMap_linear`, `existsUnique_derivedShift`, `derivedShift_obj`, `existsUnique_coneAction`, `coneMaps_linear`, `exists_derivedHasShift`, `forget_inverts`, `existsUnique_extensionMap`, `extensionMap_laws`, `extension_homotopy`, `existsUnique_actionCounit`, `sliceEssentiallySmall`, `existsUnique_restrictedAlgebra`, `existsUnique_restrictedAction`, `restrictMap_linear`, `existsUnique_derivedRestriction`.

Validation: scompile.py compiled every delivered Lean file in sandbox and library module
modes with no warnings. deliver2.py --no-push reported OK, preflight and compilation passed
(commit 605184b3f84 before removal of two unused comma imports).


## Returned delivery repair

Return L for immutable head 09e4ac77fcd1 requested a whole-proof `sorry` for
CategoryTheory.SheafDg.derivedShift_obj. I read that immutable module from the server
and compared it byte-for-byte with the retained sandbox: they agree. Neither contained
an explicit theorem of that name; the object equality was instead proved inline in
shiftObjectIso. The repair extracts that equality into the named theorem derivedShift_obj,
with its source and natural-language proof in the docstring and its Lean proof exactly
`:= by sorry`. shiftObjectIso now uses this theorem for that equality. The theorem is
listed in lean.declarations. Definitions retain actual data and the node statement,
hypotheses, dependencies, and shift/cone conventions are unchanged. The current main
node was also compared with the sandbox: only the authorized lean record differs.

Repair validation: scompile.py compiled the delivered module in sandbox and library
modes without errors or warnings. deliver2.py --no-push reported OK for commit
2948b0f15b6: preflight and compilation passed.
