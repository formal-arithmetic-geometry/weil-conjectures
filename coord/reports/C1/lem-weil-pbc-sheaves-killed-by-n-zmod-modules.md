## Worker report

The module states the identification for a scheme `T` and integer `n ≥ 1`, using the
Mathlib small étale site, the constant sheaf of rings on `ULift (ZMod n)`,
`SheafOfModules`, and its underlying sheaf of abelian groups. The first conjunct
states sectionwise annihilation by `n`; the second gives a unique module-sheaf
object whose underlying sheaf is a given sectionwise `n`-killed abelian sheaf; the
third states bijectivity on hom sets, hence full faithfulness.

The dependencies used are `AlgebraicGeometry.Scheme.smallEtaleTopology`,
`CategoryTheory.constantSheaf`, `SheafOfModules`, and `CategoryTheory.Sheaf`,
recorded by the dependency nodes. The sheaf value at `U` is rendered by
`((SheafOfModules.toSheaf O).obj G).1.obj U`; scalar annihilation is `n • s = 0`.
The edge cases `n = 1`, zero sections, and empty sheaf sections are included by
`1 ≤ n`, universal section quantification, and no nonemptiness assumptions.

Searches: `msearch.py leanfinder` and `loogle` for sheaf modules over `ZMod n`
found only generic `SheafOfModules` and group-level `AddCommGroup.zmodModule`;
grep of Mathlib and `WeilConjectures` found no sheaf equivalence; `rg` over
`lean/Sheaf` found no existing theorem. Therefore a new statement module was
written.

## Earlier second reading (a previous round; superseded)

Read the node and module together. The scheme, positive integer, constant ring
sheaf, module-sheaf category, underlying abelian sheaf, sectionwise killing,
existence/uniqueness, and bijective underlying hom map all occur in the Lean
signature. No proof beyond `sorry` is supplied.

## Second reading by C1

Read the sandbox node, its eight proof steps, the original module, and all five
statement-dependency nodes with their recorded declarations. The node itself is
correct and unchanged; this reading repairs its Lean rendering, not its statement.
No new definition nodes or dependency modules are needed.

Source check: the repository does not contain the fetched Stacks files on this
machine. I read the local source copy /home/ubuntu/c1-stacks-review, including the
tag table: 03RW is etale-cohomology-definition-constructible (lines 11672ff),
03SC is etale-cohomology-theorem-vanishing-affine-curves (lines 15656ff).
Definition 03RW introduces an arbitrary scheme; its Noetherian coefficient-ring
condition concerns constructibility, not the identification here (Z/n is itself
Noetherian). The proof of 03SC passes from an ell-killed abelian sheaf to an
F_ell-vector-space sheaf. Its field, dimension, separation, finite-type and
constructibility assumptions belong to that cohomology theorem and are not
hypotheses of the elementary module identification. I also read
sites-modules.tex, definition-presheaf-modules (676ff) and
definition-sheaf-modules (782ff): sectionwise unital module structures compatible
with restrictions, with linear natural transformations as morphisms, exactly as
used by this node. The identification is explicitly agent-formulated in the node,
rather than a separately stated Stacks theorem.

Object/hypothesis/clause list and Lean matching (all verdicts PASS after repair):

1. Arbitrary scheme T, with no geometric restrictions: `(T : Scheme.{u})`.
   `Scheme.smallEtaleTopology` is the exact recorded dependency declaration;
   I opened Mathlib.AlgebraicGeometry.Sites.Etale, whose definition is the
   small Grothendieck topology induced by Etale, and its Etale objects.
2. Positive integer n: `(n : ℕ) (hn : 1 ≤ n)` represents exactly integers n >= 1.
   No primality, characteristic, invertibility or field assumption is added.
3. The constant ring sheaf (Z/n)_T: the repeated term
   `(constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
   (RingCat.of (ULift.{u + 1} (ZMod n)))`.
   I opened ConstantSheaf.lean: constantSheaf is Functor.const followed by
   presheafToSheaf. ULift only changes the universe, preserving the ring.
4. The category Mod(T_et,Z/n): `SheafOfModules.{u + 1}` of that ring sheaf.
   Opened Mathlib.Algebra.Category.ModuleCat.Sheaf (33ff) and Presheaf (43ff).
   Its val.obj U is an O(U)-module, its maps are semilinear restriction maps,
   and its underlying abelian presheaf satisfies the sheaf condition.
   This is the dependency's notion, not the distinct fixed-ring ModuleCat-valued
   sheaf encoding used elsewhere in the source.
5. The category Ab(T_et) and forgetful functor:
   `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}` and
   `SheafOfModules.toSheaf` of the same constant ring sheaf.
   Opened Sites/Sheaf.lean (Sheaf is the full subcategory of sheaf presheaves),
   and ModuleCat/Sheaf.lean (90ff, toSheaf forgets the module structure).
   The mixed EtaleSheaves dependency explicitly records these existing notions;
   its new locally-constant/constructible predicates are not needed here.
6. Clause (1), n times identity zero: first conjunct, for every G, U and
   `s : G.val.obj U`, `n • s = 0`. Module val.obj U and the forgotten sheaf's
   sections have definitionally the same underlying abelian group. Equality of
   sheaf morphisms is sectionwise equality, so this is precisely n id = 0.
7. Clause (2), any n-killed F has exactly one module structure keeping its
   abelian sheaf fixed: second conjunct quantifies F, assumes sectionwise
   annihilation, and states `∃! G, (SheafOfModules.toSheaf ...).obj G = F`.
   Equality fixes the abelian groups and restriction maps, rather than merely
   an isomorphism class. Bundled modules supply unital actions extending those
   groups; proof fields are irrelevant, so uniqueness means uniqueness of action.
8. Clause (2), the constant residue of any integer a acts as a: third conjunct
   quantifies every G, U, `(a : ℤ)` and section s. The component at U of
   `toSheafify` on `Functor.const ... (RingCat.of (ULift (ZMod n)))`, applied to
   `ULift.up (a : ZMod n)`, acts as `a • s`. This is the canonical iota_U of
   the node, with all lifts a covered. Stating it for every module sheaf also
   covers the unique structure just asserted; step 3 of the node proves exactly
   this universal formulation. The original draft OMITTED this clause.
9. Clause (3), every abelian-sheaf map between forgotten objects is linear:
   fourth conjunct gives `Function.Bijective` for toSheaf.map on the indicated
   hom sets. Surjectivity supplies a linear lift; injectivity supplies
   faithfulness. Module morphisms are the recorded dependency's linear maps,
   and this functor preserves their underlying additive maps.
10. Consequences, fully faithful and image the full subcategory killed by n:
    hom-set bijectivity is exactly full faithfulness; clause (1) and clause (2)
    describe the strict image. The fifth conjunct additionally states
    `toSheaf.essImage F ↔ ∀ U s, n • s = 0`, accounting explicitly for invariance
    under abelian-sheaf isomorphism.
11. Final consequence, abelian isomorphisms lift to module-sheaf isomorphisms:
    sixth conjunct, for each `i : forget(G) ≅ forget(G')`, there exists
    `j : G ≅ G'` with `toSheaf.mapIso j = i`. This asserts that the given
    isomorphism, not just some unrelated isomorphism, lifts.

Edge cases: n = 0 is excluded by the node itself and by hn; n = 1 is included
and forces every section to be zero. Zero sheaves and zero sections are included.
The empty scheme and the empty etale object have no nonemptiness assumptions;
sheaf sections on an empty cover are the singleton abelian group, consistent
with the zero constant ring and module action. No cover index or finite/inhabited
index constraint was introduced. Scheme and sheaf universes use the dependency's
standard Scheme.{u}/values.{u+1} encoding, with ULift.{u+1} explicitly fixing the
coefficient universe. No variable or universe is implicit or unbound. Arbitrary
characteristics, including those dividing n, remain covered.

Independent searches, using wording different from the worker's:

- msearch.py leanfinder: "constant ring sheaf quotient integers forgetful abelian
  sheaves full image annihilated". Eight hits: chiefly condensed constant-functor
  fullness and SheafOfModules.fullyFaithfulForget. The latter forgets to presheaves
  OF MODULES over the same ring sheaf, as verified in its signature; it is not
  fullness of toSheaf to abelian sheaves. No match.
- msearch.py loogle: "SheafOfModules.toSheaf". Twelve hits: toSheaf, faithfulness,
  additive and limit properties and reflection of isomorphisms, but no fullness
  for the constant Z/n ring or killed-by-n image identification. Opened toSheaf.
- msearch.py leansearch: "abelian sheaf annihilated integer constant ring sheaf
  unique module action". Service returned Internal Server Error; unavailable,
  recorded without a negative verdict. LeanFinder, Loogle and source grep worked.
- rg for ZMod, zmod, killed_by_n and toZModLinearMap in Mathlib's ModuleCat and
  Sites directories, the project's lean/Sheaf, the source WeilConjectures, and
  dag/lean_names_upstream.json. No duplicate of this statement. Source
  AlgebraicGeometry/Curve/Reductions.lean (153ff) uses ModuleCat-valued sheaves and
  sheafCompose forgetting coefficients; it does not assert this identification.
  The project ConstructibleTorsionModulesAgree cites this item, rather than
  providing it. Existing group-level ZMod lemmas are the proof ingredients,
  not the sheaf statement. All notions therefore reuse their existing declarations.

Repairs: added the missing constant-action clause with the canonical sheafification
unit; made the essential-image and isomorphism consequences explicit; removed all
three statement-level let binders by writing out existing terms; expanded the
statement docstring to all eight proof steps with their dependency ids; added the
standard license header; replaced the unrelated EtaleSheaves import by Mathlib's
AffineEtale (site/sheafification instances) and ConstantSheaf imports, and reduced
ZMod import to Data.ZMod.Basic. No private definition or hollow definition was
introduced. The single theorem remains `by sorry`: nothing is proved at stage 2.
The node's lean.statement is copied verbatim from the final signature. The node's
mathematical statement, proof, sources and dependencies are unchanged.

Validation: scompile.py compiled the final 98-line module on the server in
3.1 seconds, exit code 0, with no errors or warnings. The final file has no
statement-level let, no line over 100 characters, and exactly one named sorry.
