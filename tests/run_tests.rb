def print_deliminater
	puts "\n------------------------\n"
end

def print_test_results(passed, failed)
	print_deliminater
	puts "\nPassed: #{passed}\n"
	failed.each do |failure|
		print_deliminater
		puts "\nFailed: #{failure[:test_name]}\n#{failure[:message]}"
	end
	print_deliminater
end

passed_tests = []
failed_tests = []

(input_dir = Dir["inputs/test_*.emi"].sort).each do |input|
	test_name = input[7...(input.length - 4)]
	puts "Ruuning: #{test_name}\n"

	# Compile the program
	output = `../emeraldic "#{input}"`

	# Run the rubevm
	output = `emeraldvm #{test_name}.evm` if output.empty?

	if (out_dir = Dir["outputs/#{test_name}/*.out"]).empty?
		output_file = "outputs/#{test_name}.out"
		if File.exist? output_file
      passed = (expected_output = File.read(output_file)) == output
      message = "Expected:\n#{[expected_output]}\nBut output was:\n#{[output]}" unless passed
      passed_tests << test_name if passed 
      failed_tests << {test_name: test_name, message: message} unless passed
    else
      failed_tests << {test_name: test_name, message: 'Test result not found in output directory'}
    end
	else
		passed = false
		expected_outputs = []

		out_dir.find do |output_file|
			passed ||= (expected_output = File.read(output_file)) == output
			expected_outputs << expected_output unless passed
			passed
		end
		unless passed
			message = "Expected one of: #{expected_outputs}\nBut output was:\n#{[output]}"
		end
		message = "Expected one of: #{expected_outputs}\nBut output was:\n#{[output]}"
		passed_tests << test_name if passed 
    failed_tests << {test_name: test_name, message: message} unless passed
	end
end

number_passed = passed_tests.count
print_test_results passed_tests, failed_tests
puts "\nResult: (#{number_passed} / #{input_dir.count}) - #{(number_passed.to_f / input_dir.count) * 100}%"

`rm *.evm`


