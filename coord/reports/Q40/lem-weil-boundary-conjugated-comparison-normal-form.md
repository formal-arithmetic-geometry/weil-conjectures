## Worker report

Item: lem-weil-boundary-conjugated-comparison-normal-form. Group Q40, stage 2.

The module Sheaf.CategoryTheory.BoundaryConjugatedComparisonNormalForm constructs
`CategoryTheory.BoundaryConjugatedComparison.rightIso` (the node's Xi) and
`CategoryTheory.BoundaryConjugatedComparison.leftIso` (the node's a), using real
composites of Mathlib natural isomorphisms. The only postponed theorem is
`CategoryTheory.BoundaryConjugatedComparison.normalForm`; its proof is `sorry`.
The theorem's docstring gives all four proof steps of the DAG node. No new node,
dependency repair, statement correction, or additional hypothesis is needed.
Only the item's `lean` field changes.

Hypothesis-by-hypothesis correspondence:

- The six categories are `CX`, `CY`, `CB`, `DX`, `DY`, `DB`, each with its own
  explicitly bound object universe and morphism universe and `Category` instance.
  There is no size identification, nonemptiness assumption, or smallness assumption.
- The source-target pairs f=(X,Y), g=(Y,B), c=(X,B) are encoded by the typed
  binders `Ff : CX ⥤ CY`, `Fg : CY ⥤ CB`, `Fc : CX ⥤ CB`,
  `Rf : CY ⥤ CX`, `Rg : CB ⥤ CY`, `Rc : CB ⥤ CX`, and their corresponding
  `Pf`, `Pg`, `Pc`, `Qf`, `Qg`, `Qc` between the D categories.
- `SX : CX ⥤ DX`, `SY : CY ⥤ DY`, `SB : CB ⥤ DB` encode S_i.
  Mathlib `Functor` includes preservation of identities and composition.
- The three rho binders have types `Rf ⋙ SX ≅ SY ⋙ Qf`,
  `Rg ⋙ SY ≅ SB ⋙ Qg`, `Rc ⋙ SX ≅ SB ⋙ Qc`. This reverses the textual
  functor order because `F ⋙ G` means G after F. The node's rho directions
  are unchanged.
- The B binders similarly have types `Ff ⋙ SY ≅ SX ⋙ Pf`,
  `Fg ⋙ SB ≅ SY ⋙ Pg`, `Fc ⋙ SB ≅ SX ⋙ Pc`.
- `α : Ff ⋙ Fg ≅ Fc` and `θ : Rc ≅ Rg ⋙ Rf` give exactly the two
  composition comparisons. An isomorphism in the Mathlib functor category
  is a natural isomorphism with mutually inverse components.
- `εc : Rc ⋙ Fc ⟶ 𝟭 CB` is the natural transformation epsilon_c.
  It is not assumed to be an adjunction counit or invertible.
- `m : ∀ H : CB, Pc.obj (Qc.obj (SB.obj H)) ⟶ SB.obj H` is the family m_H.
  It is only a family of morphisms: no naturality or invertibility is imposed.
- `hm` says for every H that `Bc.hom.app (Rc.obj H)` followed by
  `Pc.map (ρc.hom.app H)` and `m H` equals `SB.map (εc.app H)`.
  This is precisely the single assumed square, in diagrammatic order.

Clause-by-clause correspondence:

1. `rightIso ρf ρg ρc θ` has type `(SB ⋙ Qg) ⋙ Qf ≅ SB ⋙ Qc`.
   Its first factor is `Functor.isoWhiskerRight ρg.symm Qf`, followed by the
   whiskered inverse rho_f, the SX-image of inverse theta, and rho_c.
   `Functor.associator` and its inverse bridge the intermediate bracketings.
   Naturality and invertibility are part of the resulting natural isomorphism,
   with no postponed definition data. The first conjunct of `normalForm`
   identifies its hom component with
   `Qf.map (ρg.inv.app H) ≫ ρf.inv.app (Rg.obj H) ≫
   SX.map (θ.inv.app H) ≫ ρc.hom.app H`, exactly Xi_H in the node.
2. `leftIso Bf Bg Bc α` has type `(SX ⋙ Pf) ⋙ Pg ≅ SX ⋙ Pc`.
   It is the Pg-image of inverse B_f, the whiskered inverse B_g, the SB-image
   of alpha, and B_c, with canonical associators. The second conjunct is
   the node's a_G formula in diagrammatic order:
   `Pg.map (Bf.inv.app G) ≫ Bg.inv.app (Ff.obj G) ≫
   SB.map (α.hom.app G) ≫ Bc.hom.app G`.
3. The third conjunct is the inverse comparison identity for every H:
   `ρc.hom.app H ≫ (rightIso ρf ρg ρc θ).inv.app H` equals
   `SX.map (θ.hom.app H) ≫ ρf.hom.app (Rg.obj H) ≫ Qf.map (ρg.hom.app H)`.
   Both sides go from SX(Rc H) to Qf(Qg(SB H)).
4. The last conjunct substitutes `Rc.obj H` everywhere for the node's K.
   Its left side is a_K followed by Pc(rho_c,H) followed by m_H.
   Its right side is Pg(B_f,K inverse), then B_g,FfK inverse, then
   `SB.map (α.hom.app (Rc.obj H) ≫ εc.app H)`. The last functor image is
   SB(epsilon_c,H composed with alpha_K), exactly the direct-counit normal form.
   Both sides have source Pg(Pf(SX(Rc H))) and target SB H.
5. No adjunction or mate relationship occurs among the hypotheses.
   All functor rebracketings in the constructions use canonical associators;
   their components are identities, as in the node's calculation.

Dependency declarations read and used:

- `def-nagata-category` is a Mathlib leaf, with `mathlib_match` pointing to
  `CategoryTheory.Category` in Mathlib.CategoryTheory.Category.Basic. Its full
  signature and fields (CategoryStruct, id_comp, comp_id, assoc) were read.
  `public import Mathlib.CategoryTheory.Whiskering` imports that declaration
  transitively and supplies all other standard categorical notions used here.
- The relevant full signatures and docstrings of `Functor`, `NatTrans`,
  `Iso.app`, `isoWhiskerLeft`, `isoWhiskerRight`, and `NatIso.trans_app`
  were read in Mathlib's Functor.Basic, NatTrans, NatIso, and Whiskering.
  The dependency list for proofs is identical to the statement list, so there
  is no additional proof-only module import.

Source check: read Stacks categories.tex, Definition 4.2.1, Tag 0014 (including
the category laws and the following size remark). The node explicitly records
its proof as an agent-formulated categorical calculation; Bhatt--Scholze
Corollary 5.1.6 supplies geometric context only. Also read the current blueprint's
sec-smooth-purity/sk-lem-sp-tower/cor-weil-boundary-duality-discharge.proof.md and
sec-six-functors-basics/sk-prop-sf-biduality-general/_section.md under
literature/blueprint/latest, to distinguish that context from the formal lemma.

Edge cases checked before writing:

- Empty categories: all constructions are functorial whiskerings and compositions;
  no object is chosen and the universal component equations remain meaningful.
- Terminal/discrete categories and identity comparisons: both pastings reduce to
  identities. The last equation is the assumed square with the unchanged alpha
  factor, so it imposes no additional mate law.
- Noninvertible epsilon and m: neither is cancelled, inverted, or treated as an
  isomorphism. Only rho, B, alpha and theta enter the isomorphism constructions.
- Independent alpha and theta: the inverse identity uses theta, while the counit
  normal form uses alpha and hm. No compatibility between the two is needed.
- Six independently sized categories: all twelve universes are explicit;
  `set_option autoImplicit false` rejects any auto-bound implicit variable.

Searches made (2026-10-24):

- msearch.py leanfinder: "Conjugating composition natural isomorphisms by comparison
  natural isomorphisms and simplifying a counit square". Eight hits, including
  conjugateEquiv_counit, conjugateEquiv_counit_symm, Equivalence.trans_counitIso,
  and Adjunction.comp_counit. None is exact: these require adjunction/equivalence
  data, unlike the present calculation.
- msearch.py loogle: `"NatIso", "trans"`. Twelve hits, led by NatIso.trans_app,
  NatIso.op_trans and NatIso.unop_trans. They are construction identities rather
  than the two comparison formulas and both requested equations.
- msearch.py grep in CategoryTheory:
  `isoWhiskerLeft_trans|isoWhiskerRight_trans|conjugateEquiv_counit`.
  Seven hits in Whiskering, Adjunction.Mates, and Monoidal.Closed.Basic;
  only the whiskering operations are relevant building blocks. Read the actual
  mate-counit signatures to check that they add assumptions absent here.
- rg in lean/WeilConjectures and lean/Sheaf for conjugated comparison/counit names,
  together with grep for the exact item id in lean/WeilConjectures. No exact
  existing declaration was found. Read in particular
  WeilConjectures.CategoryTheory.CounitComparisonComposition (counit/model
  comparisons with extra compatibility hypotheses),
  Sheaf.CategoryTheory.InverseComparisonCounitTransport (a different two-stage
  comparison square), CompositorEquivalenceConjugation (cocycle transports), and
  ExchangeTransportCompositionConjugation (point transport recurrence).
  None states this six-category four-factor calculation under a single square.
- Exact proposed namespace/name searches in Mathlib CategoryTheory,
  lean/WeilConjectures and lean/Sheaf found no collision.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q40

I reread the node and the written file, checking each source and target and reversing
all displayed products from functional order to Mathlib's diagrammatic order.
The checks above account for every binder and all four component equations.
In particular theta is Rc -> Rg followed by Rf, epsilon is Rc followed by Fc -> id,
and the last image is SB(alpha followed by epsilon), not the reverse product.
The right and left comparisons use the inverse rho_g and B_f respectively as
first factors; both associator directions match their intermediate functors.
No mismatch was found in this self-review. No independent worker reading is
claimed: the dispatch brief explicitly prohibits starting other agents and assigns
independent review to the maintainer after this self-delivery.

Validation is performed only through scompile.py and the prescribed deliver2.py
dry run; no local compiler or global build is used.

Compiler repair: the first run found unqualified whiskering constructors;
qualified all six occurrences with `Functor.`. No signature or mathematical
statement changed.

scompile.py passed both the sandbox and final module-path checks cleanly
(1.0 seconds and 0.9 seconds respectively), with no errors or unexpected warnings.
