## Worker report

This delivery states `def-pur-roots-of-unity-sheaf` in
`Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`, together with its three genuinely
unstated prerequisites. It defines all data explicitly; every new theorem has only
`sorry` as its proof. No node statement, dependency list, proof or status was changed.
All postponed facts are clauses or construction obligations of the owning existing
node, whose blueprint id and source are in their docstrings. There are no new nodes.

The source read was Stacks 03PK, the opening definition of the functor of roots of unity
and its kernel description; 03P4, kernels of abelian sheaves; and 03CY, the unique
extension of a module action to the sheafification of the coefficient ring. The local
literature TeX files are unavailable, so the corresponding Stacks tag pages were read.
The node's pro-etale interpretation is the small site specified by the coefficient-twist
blueprint. Unlike the exactness assertion later in 03PK, this definition needs no
invertibility assumption on N.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A scheme S is `(S : Scheme.{u})`; its full small pro-etale site is `S.ProEt` with
  `ProEt.topology S`. No affine, nonempty, characteristic, invertibility or finiteness
  hypothesis is added. Positive exponents use `(N : ℕ) (hN : 0 < N)` in the module and
  transition constructions. The power and kernel themselves extend harmlessly to N=0.
- `O_S(U) = Γ(U,O_U)` is `proEtaleStructurePresheaf`: the opposite of the forgetful
  functor to schemes followed by `Scheme.Γ`. Its restriction on a scheme morphism is
  `Scheme.Γ.map`, namely `appTop`. `proEtaleStructureSheaf` bundles precisely this
  presheaf with the named sheaf-condition theorem.
- `G_m = O_Sˣ` is `proEtaleUnitsPresheaf`, composing that same ring presheaf with
  `forget₂ CommRingCat CommMonCat`, `CommMonCat.units`, `CommGrpCat.toAddCommGrp` and
  `AddCommGrpCat.uliftFunctor`. Hence its sections are
  `ULift (Additive Γ(U,O_U)ˣ)`, and restrictions are exactly the maps on units of the
  global-sections ring maps. The lift changes size only; additive addition denotes
  multiplication of units. `proEtaleUnitsSheaf` bundles the named descent theorem.
- The sectionwise power morphism `[N]` is `proEtaleUnitsPower S N = N • 𝟙 G_m`.
  This is a genuine morphism of abelian sheaves, so additivity and commutation with
  restrictions are built into its type.
- `μ_{N,S} = ker [N]` is `proEtaleRootsOfUnitySheaf`, using the recorded dependency's
  Mathlib categorical kernel, not a second kernel notion.
  `proEtaleRootsOfUnityInclusion` is exactly `kernel.ι`.
- The displayed section group is formalized by
  `existsUnique_proEtaleRootsOfUnitySections` and `proEtaleRootsOfUnitySections`.
  The additive equivalence to `Additive (rootsOfUnity N Γ(U,O_U))` is uniquely fixed
  by its composite with the kernel inclusion. Thus neither an arbitrary isomorphism
  nor an unknown root-of-unity object is selected. The restriction maps are those
  inherited from the kernel inclusion, a natural sheaf morphism.
- The statement that every section is killed by N is `proEtaleRootsOfUnity_nsmul`.
  `proEtaleRootsOfUnityModule` applies the dependency's canonical unique action to
  this same sheaf, producing a `ringedSiteModules` object over
  `proEtaleRootsOfUnityCoefficientRing S N`, the explicitly u+1-valued specialization
  of `constantZModRingSheaf (ProEt.topology S) N`.
- For `N ∣ N'`, with both positive, `proEtaleRootsOfUnityTransition` is the canonical
  `kernel.lift` of the inclusion of μ_{N'} followed by `(N'/N) • 𝟙 G_m`.
  `proEtaleRootsOfUnityTransition_condition` is its well-definedness equation;
  its docstring gives `(u^(N'/N))^N = u^N' = 1`. The kernel-lift construction fixes
  the arrow, including its restrictions and group-homomorphism property.
- `proEtaleRootsOfUnity_nsmul_of_dvd` gives the N'-torsion assertion for the target.
  `proEtaleRootsOfUnityTransition_linear` states linearity over the larger constant
  ring, with both scalar actions explicitly the uniquely determined N'-actions.
  `proEtaleRootsOfUnityTransitionModule` bundles this very arrow as a morphism of
  sheaves of modules; no arbitrary linear map is introduced.
- A prime ℓ is `(ℓ : ℕ) (hℓ : ℓ.Prime)`.
  `proEtaleRootsOfUnityTransition_prime` specifies that consecutive prime-power
  transitions are multiplication by ℓ in additive notation, i.e. u ↦ u^ℓ.
  `proEtaleRootsOfUnityTower` uses `Functor.ofOpSequence` to give a genuine
  `ℕᵒᵖ`-indexed inverse system with term `μ_{ℓ^(r+1)}`. Thus the index r=0
  corresponds to the node's first index r=1; no initial term is omitted.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`: its documented site is exactly
  `Scheme.ProEt` / `ProEt.topology`, and its constant coefficients use the ambient
  u+1 universe. The current server source was also read using `scompile.py --source`.
- The three prerequisite modules supplied below; their declarations are used directly.
- `Mathlib.CategoryTheory.Sites.Abelian`, `CategoryTheory.sheafIsAbelian`, and
  `Mathlib.CategoryTheory.Limits.Shapes.Kernels`, `CategoryTheory.Limits.kernel` and
  `kernel.ι`/`kernel.lift`: the recorded abelian-sheaf-kernel match. The source of
  `Sites.Limits` was checked for the creation of limits by the inclusion.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  the exact `SheafOfModules` abbreviation for arbitrary sites.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`:
  the sheafification of the constant presheaf, with `toSheafify` as its scalar unit.
- `Mathlib.RingTheory.RootsOfUnity.Basic`, `rootsOfUnity`, the subgroup of units
  satisfying `u^N=1`, used in the canonical sectionwise identification.

Edge cases checked before constructing the module:

- N=1: the kernel of the identity is zero; its unique module structure is over the
  zero ring ZMod 1. No nontrivial-ring assumption appears.
- Empty scheme and empty test scheme: the section ring can be the zero ring, whose
  units and roots groups are trivial; the definitions still apply.
- N divisible by the residue characteristic: roots may fail to be etale or reduced,
  but this is just the kernel sheaf, so no invertibility assumption is necessary.
- N=N': the quotient exponent is 1 and the transition is the canonical identity
  induced on the kernel. N=1 as target gives the unique map to the zero sheaf.
- The inverse system begins with μ_ℓ, and ℓ is positive because it is prime.
- Site object and arrow universes are the actual `ProEt` universes; group values
  are lifted to u+1. No artificial equality of site universes is imposed. The
  torsion module theorem is stated on an arbitrary site, with independent object,
  arrow and coefficient universes and the sheafification structure needed to
  form the constant ring sheaf.

Searches actually run:

- `msearch.py leanfinder`: "The sheaf of N-th roots of unity on the small pro-etale
  site of a scheme, kernel of the power map on units". Eight hits, including scheme
  modules and sheaf cohomology; none defines this pro-etale sheaf.
- `msearch.py loogle`: `rootsOfUnity, CommMonCat.units, CategoryTheory.Limits.kernel`.
  Zero hits for the combined query.
- `msearch.py grep`: `rootsOfUnity|unitsSheaf|rootsOfUnitySheaf`, subdirectory
  `AlgebraicGeometry`. Zero Mathlib hits there.
- `msearch.py leansearch`: "pro-etale structure sheaf of global sections and units
  sheaf; an N-torsion abelian sheaf has a unique module structure over the constant
  sheaf ZMod N". Service unavailable: Internal Server Error; not counted as no match.
- `msearch.py grep`: `proEtaleStructure|proEtaleUnits|torsionSheafModule|zmodModule|def units`.
  Twenty-five hits, mostly unrelated units constructions; the ZMod module instances
  concern individual groups rather than sheaves over a sheafified ring.
- `rg` in Mathlib's Sites, Grp, ModuleCat and RootsOfUnity sources found the primitive
  units functor, ring-to-module constructors, categorical kernels and `rootsOfUnity`;
  those primitives are reused. No existing complete pro-etale construction was found.
- `rg` in the upstream `WeilConjectures` sources and the project's `lean/Sheaf`, plus
  the upstream declaration index, found `Scheme.rootsOfUnitySheaf` in
  `WeilConjectures.AlgebraicGeometry.Sites.Kummer`, whose full definition was read:
  it is a kernel on `X.smallEtaleTopology`, not on `ProEt.topology X`. Similarly the
  upstream `unitsSheaf` uses the Zariski site and `gmSheaf` the small etale site.
  They do not define this node's objects. A blueprint-id grep in upstream found no
  declaration of the item. Searches of the new full declaration names found no clash.
- `scompile.py --source` was tried for each of the three proposed prerequisite
  module names; the current server reported all three unavailable. The repository
  records likewise contained no declaration or Mathlib match for these prerequisites.

No statement dispute or correction was needed. Initial compilation exposed an
unresolved coefficient-universe metavariable in the module-object signature; the
constant ring was explicitly specialized to u+1, the existing coefficient universe.
This imposes no equality between site object and arrow universes. Compilations and
the final dry-run result are recorded below after checking every delivered file
with `scompile.py`.

## Dependency modules

`def-pur-proetale-structure-sheaf`: no declaration or match was recorded. The module
`Sheaf.AlgebraicGeometry.ProEtaleStructureSheaf` supplies exactly the prescribed
commutative-ring presheaf of global sections and its ring-map restrictions, together
with the named sheaf-condition theorem. The theorem's docstring gives the source
argument through representability and fpqc descent.

`def-pur-proetale-units-sheaf`: no declaration or match was recorded. The module
`Sheaf.AlgebraicGeometry.ProEtaleUnitsSheaf` takes units sectionwise of that same
structure sheaf. Additive notation and ULift merely encode this group in the abelian
sheaf category. The named sheaf-condition theorem contains the node's gluing-units-
and-inverses proof in its docstring.

`lem-pur-torsion-sheaf-constant-module`: no declaration or match was recorded. The
module `Sheaf.CategoryTheory.TorsionSheafConstantModule` states unique module structures
on the fixed underlying section groups, normalized for every integer representative
and semilinear along every restriction. The unique action is then bundled using
`PresheafOfModules.ofPresheaf`; its underlying presheaf is the original F. The morphism
clause states linearity for any two such normalized actions, and the converse theorem
states that every module over the constant Z/N ring sheaf is N-torsion. The proof
of each theorem is postponed, with the full 03CY argument in its docstring.

## Validation

All four delivered modules passed the prescribed `scompile.py` together in dependency
order, each compiled separately in sandbox and library form. The final pass had no
errors or warnings; the longest individual invocation took 7.2 seconds. All declared
universes are explicit; scratch-only universe-printing checks are outside the delivery.
Node copies differ from the repository only in `lean`, with signatures copied verbatim
from the final files. The required `deliver2.py --no-push` preflight follows.

Final dry run: `deliver2.py Q16 def-pur-roots-of-unity-sheaf --no-push` printed
`OK (dry run)` for temporary commit `280414e8f5`: all four modules compile and the
preflight passes except for the independent second reading, which the next worker
writes. Nothing was pushed. The sole signature-format mismatch from the first
preflight was repaired by recording the signature from the `def` keyword, as the
preflight's signature reader requires.


## Second reading by Q16

I am the independent second reader; I did not write these modules. I opened the four
node records, all four complete modules, and every external statement-dependency
record. No mathematical mismatch or missing clause was found. I have preserved the
Lean and node copies, adding this independent review and its validation evidence.
There are no new nodes and no statement_change, so no correction-citer audit applies.

Sources read independently: Stacks 03PK, 03P4, 03CY and 098K, followed by the actual
`etale-cohomology.tex`, `sites-modules.tex` and `proetale.tex` from the Stacks project's
public source, saved only under this sandbox's scratchpad. In particular I read
`section-kummer`, `definition-additive-sheaf`, `lemma-representable-sheaf-fpqc`, and
`lemma-sheafification-presheaf-modules`. The definition in the opening of 03PK applies
to arbitrary schemes and natural exponents. The invertibility assumption belongs to
the subsequent exactness theorem and is not an assumption of this node. The source
03CY applies to a general site and a presheaf of rings, and supplies both uniqueness
of the extended action and extension of morphisms.

My statement inventory, matched against the Lean, is as follows. Verdicts apply to
the signatures and bodies, not merely to their names.

1. **Base and site.** An arbitrary scheme S and its small pro-etale site occur as
   `(S : Scheme.{u})`, `S.ProEt`, and `ProEt.topology S`. I read Mathlib's `ProEt`
   definition (the category of weakly etale objects over S), its forgetful functor,
   and its topology. These are the exact objects of both site dependency nodes.
   I also read `Scheme.proEtaleDerivedCategory`, including the current server source
   through `scompile.py --source`: its documented site is this same site. PASS.
2. **Positive integer N.** The module and transition declarations bind `(N : ℕ)`
   with `(hN : 0 < N)`, and the latter also bind positive N'. The power morphism and
   kernel themselves are defined for all natural N; their positive specializations
   are precisely the requested objects. There is no extra condition on S or N. PASS.
3. **Structure sheaf and restrictions.** `proEtaleStructurePresheaf` is literally
   `(ProEt.forget S ⋙ Over.forget S).op ⋙ Scheme.Γ`. I read `Scheme.Γ`, whose object
   is the ring of global sections and whose map is pullback on global sections.
   `proEtaleStructureSheaf` bundles this presheaf and its named sheaf theorem,
   without replacing it by an abstract ring sheaf. PASS.
4. **Units sheaf.** `proEtaleUnitsPresheaf` takes units of that precise ring
   presheaf. `CommGrpCat.toAddCommGrp` and `AddCommGrpCat.uliftFunctor` change notation
   and size; its sections remain the units of Γ(U,O_U), and restrictions are the
   induced maps on units. `proEtaleUnitsSheaf` bundles descent for these sections.
   I checked the separate dependency node, including its gluing-inverses argument,
   against this module and 03P4(2). PASS.
5. **Power map and kernel.** `proEtaleUnitsPower S N = N • 𝟙 _` is the sectionwise
   power homomorphism in additive notation; its sheaf-morphism type supplies
   naturality. `proEtaleRootsOfUnitySheaf` is exactly `Limits.kernel` of this map,
   and `proEtaleRootsOfUnityInclusion` is its `kernel.ι`. I read the recorded
   `sheafIsAbelian` match and the limits-creation instance in Sites.Limits. PASS.
6. **Section formula and inherited restrictions.**
   `existsUnique_proEtaleRootsOfUnitySections` specifies an additive equivalence
   with `Additive (rootsOfUnity N Γ(U,O_U))`, and fixes it by its composite with
   the actual kernel inclusion into units. Mathlib's `rootsOfUnity` is precisely
   the subgroup of units with N-th power one, including for N=0. The chosen
   `proEtaleRootsOfUnitySections` is determined uniquely by this condition.
   Naturality of the kernel inclusion forces the inherited restriction maps;
   there is no independent restriction law or arbitrary identification. PASS.
7. **N-torsion and coefficient modules.** `proEtaleRootsOfUnity_nsmul` quantifies
   over every test object U and every section x. `proEtaleRootsOfUnityModule`
   applies the supplied `torsionSheafModule` to this same sheaf. Its coefficient
   ring is `constantZModRingSheaf`, explicitly Mathlib's sheafification of the
   constant ring `ULift (ZMod N)`. I read the constantSheaf dependency and
   `ringedSiteModules`, which is exactly `SheafOfModules`, together with Mathlib's
   objects and linear morphisms. PASS.
8. **Divisibility transition.** `proEtaleRootsOfUnityTransition` binds both positive
   exponents and `h : N ∣ N'`. Its actual body is `kernel.lift` of the inclusion
   from μ_N' followed by `(N'/N) • 𝟙 G_m`. This fixes the requested power map,
   including every section and restriction. The named condition theorem states
   exactly the equation needed for this lift, with the quotient-exponent argument
   in its proof docstring. PASS.
9. **Linearity over the larger ring.** `proEtaleRootsOfUnity_nsmul_of_dvd` makes
   μ_N an N'-torsion sheaf. `proEtaleRootsOfUnityTransition_linear` uses the two
   unique N'-scalar actions, and `proEtaleRootsOfUnityTransitionModule` bundles
   the very same additive morphism over the constant Z/N' ring. In particular
   this does not incorrectly assert that the arrow has the smaller ring as
   coefficients on its source. PASS.
10. **Prime powers and inverse system.** The prime hypothesis is `hℓ : ℓ.Prime`.
    `proEtaleRootsOfUnityTransition_prime` evaluates the arrow from exponent
    ℓ^(r+2) to ℓ^(r+1), after inclusion, as multiplication by ℓ. The inclusion
    is monic, so this is the specified sectionwise ℓ-th power map.
    `proEtaleRootsOfUnityTower` is a genuine `ℕᵒᵖ`-functor using `ofOpSequence`,
    with index r corresponding to the mathematical index r+1. Its first term
    is μ_ℓ and every later term and transition is present. PASS.

The third dependency module, `lem-pur-torsion-sheaf-constant-module`, was also read
against its complete two-part node and 03CY. `IsConstantZModSheafModuleStructure`
normalizes the scalar action for **all integers** z, not just nonnegative ones,
and imposes semilinearity for every restriction. The existence-and-uniqueness
statement keeps the underlying groups fixed. The chosen family is therefore not
hollow: an ∃! theorem determines its data. `torsionSheafModuleStructure_spec`
records its characterization; `torsionSheafModule` bundles those very groups;
`torsionSheaf_hom_linear` covers every additive morphism and any normalized actions;
and `constantZModModuleSheaf_nsmul` states the converse on every object and section.
No clause of either part of the dependency node is missing. Its `[HasSheafify J
RingCat.{w}]` is the infrastructure required to form the source's constant sheaf;
object, arrow and value universes remain independent. The other two dependency
modules likewise state their existing nodes exactly, and each dependency record
explains its previously absent interface. No dependency record was silently
reinterpreted, and comparisons with the shared repository show changes only in lean.

Edge cases: no `Nonempty`, `Nontrivial`, field, noetherian, affine, finite-type or
invertibility instance is imposed. For N=1 the kernel is zero and the coefficient
ring is the zero ring ZMod 1; these modules are allowed. The empty base and empty
test scheme remain allowed, including the empty covering and its unique zero-ring
sections. N=0 is outside the positive-exponent module/transition clauses, but the
power/kernel definitions still correctly give the zero map and its full kernel.
Residue characteristic dividing N is allowed; no exactness or etaleness of μ_N is
claimed. For N=N' the quotient is 1; for N=1 the target is the zero sheaf. The
prime-power index starts at 1, with no missing μ_ℓ term. Test objects range over the
whole recorded site. The group-value lift to u+1 does not identify its object and
morphism universes or add a smallness restriction. There is no arbitrary empty
index family excluded by the sheaf definitions.

Independent searches used different descriptions from the first worker:

- `msearch.py leanfinder`: "Sheaf of units killed by a natural number on the weakly
  etale site; torsion abelian sheaf as a module over a constant quotient ring".
  Eight hits concerned general sheaf/module APIs; no matching construction.
- `msearch.py loogle`: `CategoryTheory.Sheaf, Module` returned
  `PresheafOfModules.Sheafify.module`. I opened its actual declaration: it is the
  general module structure on the sheafification of a presheaf over a ring map
  with local bijectivity assumptions. It does not state the fixed-group uniqueness
  or normalized constant Z/N action of this dependency. It can support its proof.
- `msearch.py leansearch`: "abelian sheaf killed by N unique module structure
  constant ring ZMod N" returned an internal-server error. This was recorded as
  unavailable, not as evidence of absence.
- Independent `rg` searches of upstream WeilConjectures and project lean/Sheaf for
  units, G_m, roots-of-unity sheaves, torsion module actions and constant ZMod rings
  found upstream `Scheme.rootsOfUnitySheaf` in Sites.Kummer. I opened its definition:
  its domain topology is `X.smallEtaleTopology`, so it is not this pro-etale node.
  The available Zariski units sheaf and etale G_m likewise use different sites.
  Searches for every proposed proEtaleStructure/proEtaleUnits/proEtaleRootsOfUnity
  and torsionSheafModule name found no project/upstream clash. Mathlib searches
  found and I read the existing rootsOfUnity subgroup, constantSheaf, kernel/limit
  API and SheafOfModules, all reused here. No complete duplicate was found.

H5/H6/H8/H9 checks: all definitions contain real functor/kernel/module data or a
choice characterized by an ∃! theorem. No mere existence choice defines an
uncontrolled object. Every postponed theorem is a construction obligation or an
explicit clause of its owning node, carries the source and blueprint identifier,
and gives its proof argument step by step. Every theorem proof is exactly sorry;
no proof was supplied at stage 2. All lines satisfy the 100-character limit. Every
universe and variable is bound, imports use the required module roots, and no
private copy or file-local notation/instance hides a statement dependency.

Repairs: none needed in Lean or node signatures. The change from this reading is
this explicit clause-by-clause review, independent source/search evidence, and the
fresh validation below; the Worker report remains in place.

Fresh second-reader validation: the prescribed four-file `scompile.py Q16
def-pur-roots-of-unity-sheaf ...` completed successfully for every module, separately
in sandbox and library form. There were no errors or warnings; the longest single
compile was 9.5 seconds. The node lean.statement strings remain verbatim the
signatures verified by the first dry run; no signature has changed in this reading.

Second-reader dry run: `deliver2.py Q16 def-pur-roots-of-unity-sheaf --no-push`
printed `OK (dry run)` for commit `8a2269a3b5`: all four modules compile and the
complete preflight, including the independent second reading, passes.
