# Proper projection normalization: local proof commands and new coordinates

Item: `Sheaf.Paper.IntegralProperProjectionSystemNormalization` (group V7).

The assigned module retains its existing theorem signature and public imports.
Its added `open` commands abbreviate names only within this file. Its added
`attribute [local irreducible]` commands affect only elaboration of this proof;
they do not change exported attributes, instances or reducibility. The private
helpers are proved categorical transport and pasting identities.

The four new modules provide explicitly constructed coordinate maps and three
strictly smaller public normalization statements. Each has a new DAG node. The
coordinate definitions contain no sorry. The original hole is decomposed into
three named holes, as recorded in report.md; this is not a net decrease in holes.

No existing shared definition, statement, public import, notation or instance is
changed. No existing module besides the assigned item is edited, and no downstream
adaptation is required. All five modules passed the warning-free delivery compile.

The initial node record for reduce mistakenly included its body in lean.statement;
this packet records only the declaration signature, stopping before :=.
