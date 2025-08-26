.PHONY: all clean

all: EnergyEconomics.vo ThresholdAnalysis.vo WeiEquivalence.vo KoomeySaundersResolution.vo PolicyFramework.vo

%.vo: %.v
	coqc $

EnergyEconomics.vo: EnergyEconomics.v

ThresholdAnalysis.vo: ThresholdAnalysis.v EnergyEconomics.vo

WeiEquivalence.vo: WeiEquivalence.v EnergyEconomics.vo

KoomeySaundersResolution.vo: KoomeySaundersResolution.v EnergyEconomics.vo

PolicyFramework.vo: PolicyFramework.v EnergyEconomics.vo

clean:
	rm -f *.vo *.glob *.aux