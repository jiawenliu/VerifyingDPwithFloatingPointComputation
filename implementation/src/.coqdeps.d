Environments.vo Environments.glob Environments.v.beautified: Environments.v ./Infra/ExpressionAbbrevs.vo ./Infra/RationalSimps.vo
Environments.vio: Environments.v ./Infra/ExpressionAbbrevs.vio ./Infra/RationalSimps.vio
ExpressionSemantics.vo ExpressionSemantics.glob ExpressionSemantics.v.beautified: ExpressionSemantics.v ./Infra/RealRationalProps.vo ./Infra/RationalSimps.vo ./Infra/Ltacs.vo ./Infra/ExpressionAbbrevs.vo
ExpressionSemantics.vio: ExpressionSemantics.v ./Infra/RealRationalProps.vio ./Infra/RationalSimps.vio ./Infra/Ltacs.vio ./Infra/ExpressionAbbrevs.vio
ErrorBounds.vo ErrorBounds.glob ErrorBounds.v.beautified: ErrorBounds.v ./Infra/Abbrevs.vo ./Infra/RationalSimps.vo ./Infra/RealSimps.vo ./Infra/RealRationalProps.vo Environments.vo ./Infra/ExpressionAbbrevs.vo ExpressionSemantics.vo
ErrorBounds.vio: ErrorBounds.v ./Infra/Abbrevs.vio ./Infra/RationalSimps.vio ./Infra/RealSimps.vio ./Infra/RealRationalProps.vio Environments.vio ./Infra/ExpressionAbbrevs.vio ExpressionSemantics.vio
Expressions.vo Expressions.glob Expressions.v.beautified: Expressions.v ./Infra/RealRationalProps.vo ./Infra/RationalSimps.vo ./Infra/Ltacs.vo ./Infra/Abbrevs.vo ./Infra/NatSet.vo ./Infra/MachineType.vo
Expressions.vio: Expressions.v ./Infra/RealRationalProps.vio ./Infra/RationalSimps.vio ./Infra/Ltacs.vio ./Infra/Abbrevs.vio ./Infra/NatSet.vio ./Infra/MachineType.vio
AffineForm.vo AffineForm.glob AffineForm.v.beautified: AffineForm.v ./Infra/Abbrevs.vo
AffineForm.vio: AffineForm.v ./Infra/Abbrevs.vio
TypeValidator.vo TypeValidator.glob TypeValidator.v.beautified: TypeValidator.v ./Infra/RationalSimps.vo ./Infra/RealRationalProps.vo ./Infra/Ltacs.vo ssaPrgs.vo ./Infra/ExpressionAbbrevs.vo ./Infra/RealSimps.vo ./Infra/NatSet.vo ./Infra/MachineType.vo ./Infra/Results.vo
TypeValidator.vio: TypeValidator.v ./Infra/RationalSimps.vio ./Infra/RealRationalProps.vio ./Infra/Ltacs.vio ssaPrgs.vio ./Infra/ExpressionAbbrevs.vio ./Infra/RealSimps.vio ./Infra/NatSet.vio ./Infra/MachineType.vio ./Infra/Results.vio
ssaPrgs.vo ssaPrgs.glob ssaPrgs.v.beautified: ssaPrgs.v ./Infra/RealRationalProps.vo ./Infra/Ltacs.vo ExpressionSemantics.vo
ssaPrgs.vio: ssaPrgs.v ./Infra/RealRationalProps.vio ./Infra/Ltacs.vio ExpressionSemantics.vio
ErrorAnalysis.vo ErrorAnalysis.glob ErrorAnalysis.v.beautified: ErrorAnalysis.v ExpressionSemantics.vo Environments.vo ./Infra/RationalSimps.vo TypeValidator.vo IntervalArithQ.vo
ErrorAnalysis.vio: ErrorAnalysis.v ExpressionSemantics.vio Environments.vio ./Infra/RationalSimps.vio TypeValidator.vio IntervalArithQ.vio
ErrorValidation.vo ErrorValidation.glob ErrorValidation.v.beautified: ErrorValidation.v ./Infra/Abbrevs.vo ./Infra/RationalSimps.vo ./Infra/RealRationalProps.vo ./Infra/RealSimps.vo ./Infra/Ltacs.vo Environments.vo ErrorAnalysis.vo ErrorBounds.vo IntervalArithQ.vo TypeValidator.vo
ErrorValidation.vio: ErrorValidation.v ./Infra/Abbrevs.vio ./Infra/RationalSimps.vio ./Infra/RealRationalProps.vio ./Infra/RealSimps.vio ./Infra/Ltacs.vio Environments.vio ErrorAnalysis.vio ErrorBounds.vio IntervalArithQ.vio TypeValidator.vio
OrderedExpressions.vo OrderedExpressions.glob OrderedExpressions.v.beautified: OrderedExpressions.v
OrderedExpressions.vio: OrderedExpressions.v
IntervalArithQ.vo IntervalArithQ.glob IntervalArithQ.v.beautified: IntervalArithQ.v ./Infra/Abbrevs.vo ./Infra/RationalSimps.vo
IntervalArithQ.vio: IntervalArithQ.v ./Infra/Abbrevs.vio ./Infra/RationalSimps.vio
./Infra/RealSimps.vo ./Infra/RealSimps.glob ./Infra/RealSimps.v.beautified: ./Infra/RealSimps.v
./Infra/RealSimps.vio: ./Infra/RealSimps.v
./Infra/Ltacs.vo ./Infra/Ltacs.glob ./Infra/Ltacs.v.beautified: ./Infra/Ltacs.v ./Infra/RealSimps.vo ./Infra/NatSet.vo ./Infra/RationalSimps.vo ./Infra/RealRationalProps.vo ./Infra/Results.vo
./Infra/Ltacs.vio: ./Infra/Ltacs.v ./Infra/RealSimps.vio ./Infra/NatSet.vio ./Infra/RationalSimps.vio ./Infra/RealRationalProps.vio ./Infra/Results.vio
./Infra/ExpressionAbbrevs.vo ./Infra/ExpressionAbbrevs.glob ./Infra/ExpressionAbbrevs.v.beautified: ./Infra/ExpressionAbbrevs.v ./Infra/Abbrevs.vo AffineForm.vo Expressions.vo ./Infra/Ltacs.vo OrderedExpressions.vo
./Infra/ExpressionAbbrevs.vio: ./Infra/ExpressionAbbrevs.v ./Infra/Abbrevs.vio AffineForm.vio Expressions.vio ./Infra/Ltacs.vio OrderedExpressions.vio
./Infra/NatSet.vo ./Infra/NatSet.glob ./Infra/NatSet.v.beautified: ./Infra/NatSet.v
./Infra/NatSet.vio: ./Infra/NatSet.v
./Infra/Results.vo ./Infra/Results.glob ./Infra/Results.v.beautified: ./Infra/Results.v
./Infra/Results.vio: ./Infra/Results.v
./Infra/DebugLtacs.vo ./Infra/DebugLtacs.glob ./Infra/DebugLtacs.v.beautified: ./Infra/DebugLtacs.v ./Infra/Ltacs.vo ./Infra/NatSet.vo IntervalArithQ.vo
./Infra/DebugLtacs.vio: ./Infra/DebugLtacs.v ./Infra/Ltacs.vio ./Infra/NatSet.vio IntervalArithQ.vio
./Infra/Abbrevs.vo ./Infra/Abbrevs.glob ./Infra/Abbrevs.v.beautified: ./Infra/Abbrevs.v ./Infra/MachineType.vo
./Infra/Abbrevs.vio: ./Infra/Abbrevs.v ./Infra/MachineType.vio
./Infra/RealRationalProps.vo ./Infra/RealRationalProps.glob ./Infra/RealRationalProps.v.beautified: ./Infra/RealRationalProps.v ./Infra/RationalSimps.vo ./Infra/RealSimps.vo
./Infra/RealRationalProps.vio: ./Infra/RealRationalProps.v ./Infra/RationalSimps.vio ./Infra/RealSimps.vio
./Infra/MachineType.vo ./Infra/MachineType.glob ./Infra/MachineType.v.beautified: ./Infra/MachineType.v ./Infra/RealRationalProps.vo ./Infra/Ltacs.vo
./Infra/MachineType.vio: ./Infra/MachineType.v ./Infra/RealRationalProps.vio ./Infra/Ltacs.vio
./Infra/RationalSimps.vo ./Infra/RationalSimps.glob ./Infra/RationalSimps.v.beautified: ./Infra/RationalSimps.v
./Infra/RationalSimps.vio: ./Infra/RationalSimps.v
